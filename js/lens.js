/* A lens that follows the cursor along a line of text.
 *
 * The page itself is never touched. The characters of the hovered line are
 * measured, then redrawn in an overlay sitting exactly on top of that line, and
 * only those get transformed. Nothing reflows, so lines never rewrap and the
 * rows above and below hold still.
 *
 * Magnification peaks under the cursor and eases back to exactly 1 at the rim,
 * which is what lets the overlay meet the untouched text with no visible seam.
 * The width gained under the cursor is given back across the middle of the
 * lens, so the line keeps its total width and both ends stay put.
 */
(function () {
  "use strict";

  if (!window.matchMedia) return;
  if (!matchMedia("(pointer: fine)").matches) return;      // mouse or trackpad only
  if (matchMedia("(prefers-reduced-motion: reduce)").matches) return;

  var ZOOM = 1.10;        // peak magnification, before width is given back
  var WIDTH_CH = 5;       // lens radius in characters, so it suits any font size
  var FALLOFF = 2.2;      // how tightly the magnification gathers at the cursor
  var EASE = 0.34;        // how quickly the sampled point chases the pointer
  var AMP_EASE = 0.26;    // how quickly a row fades in and out

  var lens = null, spans = [], chars = [], runs = [];
  var cacheEl = null, cacheTop = 0, cacheBottom = -1, cacheAvgW = 10, cacheVisible = 0;
  var raf = 0, px = 0, py = 0, sx = 0, sy = 0, running = false;
  var amp = 0, ampTarget = 1, lensLeft = 0;

  function bgOf(el) {
    for (var n = el; n && n !== document.documentElement; n = n.parentElement) {
      var b = getComputedStyle(n).backgroundColor;
      if (b && b !== "transparent" && !/rgba\(0, 0, 0, 0\)/.test(b)) return b;
    }
    return getComputedStyle(document.body).backgroundColor;
  }

  /* Climb from the deepest element under the cursor to the block that owns the
     line. Without this, hovering a <strong> would magnify only the bold words
     and leave the rest of the sentence flat, which reads as a broken line. */
  function blockOf(hit) {
    for (var n = hit; n && n !== document.body; n = n.parentElement) {
      var d = getComputedStyle(n).display;
      if (d === "inline" || d === "inline-block" || d === "inline-flex") continue;
      /* A flex or grid box lays its children out in columns, so its line boxes
         are not text lines. Stay with the element actually holding the text. */
      if (d.indexOf("flex") > -1 || d.indexOf("grid") > -1) return hit;
      return n;
    }
    return hit;
  }

  function hasText(el) {
    return !!(el && el.textContent && el.textContent.trim());
  }

  /* The line box under the pointer. At line-height 1 a glyph box is taller than
     the line advance, so neighbouring lines overlap; take the band whose centre
     is nearest the cursor rather than the first one that contains it. */
  function lineAt(el, y) {
    var rg = document.createRange();
    rg.selectNodeContents(el);
    var all = rg.getClientRects(), seed = null, bestD = Infinity, i, b;
    for (i = 0; i < all.length; i++) {
      b = all[i];
      if (b.width < 0.5 || b.height < 0.5) continue;
      if (y < b.top - 0.5 || y > b.bottom + 0.5) continue;
      var d = Math.abs((b.top + b.bottom) / 2 - y);
      if (d < bestD) { bestD = d; seed = b; }
    }
    if (!seed) return null;

    /* getClientRects gives one rect per inline run, not per line: a paragraph
       containing an <abbr> reports several. Union every fragment that sits on
       the same line as the seed, otherwise the band is only part of the row. */
    var top = seed.top, bottom = seed.bottom, left = seed.left, right = seed.right;
    for (i = 0; i < all.length; i++) {
      b = all[i];
      if (b.width < 0.5 || b.height < 0.5) continue;
      var mid = (b.top + b.bottom) / 2;
      if (mid < seed.top - 0.5 || mid > seed.bottom + 0.5) continue;
      /* height stays with the seed: a padded inline-block on the line would
         otherwise stretch the cover over the rows above and below */
      if (b.left < left) left = b.left;
      if (b.right > right) right = b.right;
    }
    return { top: top, bottom: bottom, left: left, right: right,
             width: right - left, height: bottom - top };
  }

  /* Screen-reader-only text is clipped to nothing, but Range still reports its
     full unclipped width, so it would join the line and throw every offset
     after it out by that amount. */
  function clipped(node, stop) {
    for (var n = node; n && n !== stop && n !== document.body; n = n.parentElement) {
      var d = getComputedStyle(n);
      if (d.clip && d.clip !== "auto") return true;
      if (d.clipPath && d.clipPath !== "none") return true;
      if (d.position === "absolute" && n.offsetWidth <= 1 && n.offsetHeight <= 1) return true;
    }
    return false;
  }

  function charsOnLine(el, band) {
    var walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT, null);
    var out = [], n, r = document.createRange(), skip = new Map();
    while ((n = walker.nextNode())) {
      var host = n.parentElement;
      if (!skip.has(host)) skip.set(host, clipped(host, el));
      if (skip.get(host)) continue;
      var t = n.nodeValue;
      for (var i = 0; i < t.length; i++) {
        r.setStart(n, i); r.setEnd(n, i + 1);
        var b = r.getBoundingClientRect();
        if (!b.width && !b.height) continue;
        var cy = b.top + b.height / 2;
        /* The band is a rectangle, and in a flex or grid row several unrelated
           runs of text share it. Anything outside the band horizontally belongs
           to a different column, or is visually hidden text parked off screen,
           and must not join this line. */
        if (cy >= band.top && cy <= band.bottom &&
            b.left >= band.left - 1 && b.right <= band.right + 1) {
          out.push({ ch: t[i], x: b.left, y: b.top, w: b.width, h: b.height,
                     owner: n.parentElement || el });
        }
      }
    }
    /* A glyph's rect is not its advance once letter-spacing is in play, and the
       offsets are built from advances. Take each step from the next character's
       origin, and keep the measured width only for the final one. */
    for (var k = 0; k < out.length - 1; k++) {
      var step = out[k + 1].x - out[k].x;
      if (step > 0 && Math.abs(step - out[k].w) < out[k].w + 4) out[k].w = step;
    }
    return out;
  }

  function destroy() {
    if (lens) { lens.remove(); lens = null; }
    spans = []; chars = []; runs = [];
    cacheEl = null; cacheTop = 0; cacheBottom = -1;
    amp = 0; ampTarget = 1;
  }

  function build(el, list, band) {
    if (lens) lens.remove();
    var cs = getComputedStyle(el);
    var minX = Infinity, maxX = -Infinity;
    list.forEach(function (c) {
      if (c.x < minX) minX = c.x;
      if (c.x + c.w > maxX) maxX = c.x + c.w;
    });

    lens = document.createElement("div");
    lens.className = "text-lens";
    lens.setAttribute("aria-hidden", "true");
    lensLeft = minX;
    lens.style.left = minX + "px";
    /* The cover has to hide every glyph on this line, or the original shows
       through above and below it and each letter is drawn twice. So it spans
       exactly what the characters occupy, no less. Sitting a shade into the
       neighbouring line's box is harmless, because that part of the box is
       ascent and descent room rather than ink. */
    var slotTop = Infinity, slotBot = -Infinity;
    list.forEach(function (c) {
      if (c.y < slotTop) slotTop = c.y;
      if (c.y + c.h > slotBot) slotBot = c.y + c.h;
    });
    if (!isFinite(slotTop)) { slotTop = band.top; slotBot = band.bottom; }
    /* and room for the growth: a magnified glyph reaches above and below the
       box it was measured in, by half its gain on each side */
    var fsB = parseFloat(cs.fontSize) || 16;
    var peakB = Math.min(0.35, (ZOOM - 1) * (52 / Math.max(fsB, 8)));
    var tallest = 0;
    list.forEach(function (c) { if (c.h > tallest) tallest = c.h; });
    var roomB = tallest * peakB / 2 + 1;
    slotTop -= roomB;
    slotBot += roomB;


    lens.style.top = slotTop + "px";
    /* Without an explicit size the box collapses, the background covers
       nothing, and the original shows through under the overlay: every glyph
       is drawn twice and the row reads as bold. The cover is the line box and
       never a pixel more, so the row above is left alone. */
    lens.style.width = (maxX - minX) + "px";
    lens.style.height = Math.max(1, slotBot - slotTop) + "px";
    lens.style.background = bgOf(el);

    /* Styles come from each character's own parent, not from the hovered
       element. A <strong> inside a list item, the number chip inside a
       heading, the accent block in the headline: all of them keep their own
       weight, colour and background this way. */
    var seen = new Map();
    function styleOf(node) {
      var hit = seen.get(node);
      if (hit) return hit;
      var d = getComputedStyle(node);
      var own = {
        /* resolved up the tree: a transparent span inside a button still
           sits on the button colour, and must join its run */
        _bg: bgOf(node),
        fontFamily: d.fontFamily, fontWeight: d.fontWeight, fontStyle: d.fontStyle,
        fontSize: d.fontSize, fontVariationSettings: d.fontVariationSettings,
        fontFeatureSettings: d.fontFeatureSettings, letterSpacing: d.letterSpacing,
        wordSpacing: d.wordSpacing, color: d.color, textTransform: d.textTransform,
        textDecoration: d.textDecoration, textDecorationColor: d.textDecorationColor,
        textDecorationThickness: d.textDecorationThickness,
        textUnderlineOffset: d.textUnderlineOffset
      };
      seen.set(node, own);
      return own;
    }

    /* A drop cap is a pseudo element, so its size and colour live nowhere in
       the character's own styles; lift them onto the first glyph by hand. */
    var firstLetter = null, firstIdx = -1;
    try {
      var fl = getComputedStyle(el, "::first-letter");
      var rg0 = document.createRange();
      rg0.selectNodeContents(el);
      var rects0 = rg0.getClientRects();
      var onFirstLine = rects0.length && Math.abs(rects0[0].top - band.top) < 1;
      if (onFirstLine && fl && fl.fontSize && fl.fontSize !== cs.fontSize) {
        firstLetter = fl;
        // the browser applies it to the first real letter, not to the newline
        // and indentation that markup usually starts a paragraph with
        for (var q = 0; q < list.length; q++) {
          if (list[q].ch.trim()) { firstIdx = q; break; }
        }
      }
    } catch (e) {}

    spans = list.map(function (c, idx) {
      var d = styleOf(c.owner);
      var s = document.createElement("i");
      s.textContent = c.ch;
      s.style.left = (c.x - minX) + "px";
      s.style.top = (c.y - slotTop) + "px";
      s.style.height = c.h + "px";
      s.style.lineHeight = c.h + "px";
      /* Width is the advance, not the ink. Otherwise an underline is drawn
         only under each glyph and the rule arrives broken into pieces. */
      s.style.width = c.w + "px";
      for (var k in d) if (k.charAt(0) !== "_" && d[k]) s.style[k] = d[k];
      if (idx === firstIdx && firstLetter) {
        s.style.fontSize = firstLetter.fontSize;
        s.style.fontFamily = firstLetter.fontFamily;
        s.style.fontWeight = firstLetter.fontWeight;
        s.style.color = firstLetter.color;
        /* keep the measured box: the pseudo element's own line-height fights
           the height the glyph was actually laid out at */
      }
      lens.appendChild(s);
      return s;
    });
    /* A run is a stretch of characters belonging to one decorated element, and
       it carries that element's whole box: background, border, radius and
       shadow. Drawing the box once per run rather than per glyph is what keeps
       it whole, and carrying the border is what lets a button or a nav link be
       magnified instead of refused. */
    runs = [];
    var pageBg = bgOf(el), start = -1, runOwner = null;
    function boxy(node) {
      if (node === el) return false;
      var d = getComputedStyle(node);
      if (parseFloat(d.borderTopWidth) || parseFloat(d.borderRightWidth) ||
          parseFloat(d.borderBottomWidth) || parseFloat(d.borderLeftWidth)) return true;
      if (d.boxShadow && d.boxShadow !== "none") return true;
      if (parseFloat(d.borderTopLeftRadius) > 0) return true;
      var b = bgOf(node);
      return !!(b && b !== pageBg && !/rgba\(0, 0, 0, 0\)/.test(b));
    }
    function closeRun(endIdx) {
      if (start < 0 || endIdx < start) { start = -1; runOwner = null; return; }
      var owner = runOwner, ob = owner.getBoundingClientRect(), d = getComputedStyle(owner);
      var b = document.createElement("b");
      b.className = "text-lens-bg";
      b.style.background = d.backgroundColor;
      b.style.borderStyle = d.borderStyle;
      b.style.borderColor = d.borderColor;
      b.style.borderWidth = d.borderWidth;
      b.style.borderRadius = d.borderRadius;
      b.style.boxShadow = d.boxShadow;
      b.style.top = (ob.top - slotTop) + "px";
      b.style.height = ob.height + "px";
      lens.insertBefore(b, lens.firstChild);
      /* the gap between the box edge and the first glyph is padding: hold it
         steady while the text inside grows */
      runs.push({ el: b, from: start, to: endIdx,
                  padL: list[start].x - ob.left,
                  padR: ob.right - (list[endIdx].x + list[endIdx].w) });
      start = -1; runOwner = null;
    }
    for (var i2 = 0; i2 < list.length; i2++) {
      var o2 = list[i2].owner, want = boxy(o2) ? o2 : null;
      if (want !== runOwner) { closeRun(i2 - 1); if (want) { start = i2; runOwner = want; } }
    }
    closeRun(list.length - 1);

    document.body.appendChild(lens);
    chars = list;
  }

  /* The overlay can redraw text. It cannot redraw a border, a shadow or a
     rounded corner, so on a line that carries any of those it would paint the
     background flat over the box and hand back only the letters. Buttons,
     chips and framed labels are left alone rather than damaged. */
  /* Borders, shadows, radii and backgrounds are all redrawn by the runs now.
     A transform is the one thing that cannot be: the measured boxes are the
     rotated bounds, so redrawing them upright would stand the words up. */
  function decorated(node, stop) {
    for (var n = node; n && n !== stop && n !== document.body; n = n.parentElement) {
      var d = getComputedStyle(n);
      if (d.transform && d.transform !== "none") return true;
    }
    return false;
  }

  function acquire(el, band) {
    var probe = charsOnLine(el, band);
    if (!probe.length) return false;
    for (var b2 = 0; b2 < probe.length; b2++) {
      if (probe[b2].owner !== el && decorated(probe[b2].owner, el)) return false;
    }
    /* The width borrowed under the cursor is paid back by the characters around
       it, and a line of three or four glyphs has nobody to pay. Growing them
       from the middle instead worked, but it took a hover fallback to reach
       them at all, and that reached too much else besides. Left alone. */
    var visible = 0;
    for (var v = 0; v < probe.length; v++) if (probe[v].ch.trim() && probe[v].w > 0) visible++;
    if (visible < 5) return false;
    var wsum = 0, wn = 0;
    for (var i = 0; i < probe.length; i++) if (probe[i].w > 0) { wsum += probe[i].w; wn++; }
    cacheAvgW = wn ? wsum / wn : 10;
    cacheVisible = visible;
    cacheEl = el; cacheTop = band.top; cacheBottom = band.bottom;
    build(el, probe, band);
    return true;
  }

  /* A line tucked under the sticky header would otherwise be drawn over it. */
  function hiddenByHeader(el, band) {
    var head = document.querySelector(".site-head");
    if (!head || head.contains(el)) return false;
    return band.top < head.getBoundingClientRect().bottom - 0.5;
  }

  /* An overlay such as a stretched card link swallows elementFromPoint, which
     then resolves to the whole card instead of the text being pointed at. Ask
     for the caret position instead: it names the text node itself. */
  function targetAt(x, y) {
    var rg = null;
    if (document.caretRangeFromPoint) rg = document.caretRangeFromPoint(x, y);
    else if (document.caretPositionFromPoint) {
      var cp = document.caretPositionFromPoint(x, y);
      if (cp) { rg = document.createRange(); rg.setStart(cp.offsetNode, cp.offset); rg.collapse(true); }
    }
    if (!rg) return null;
    var node = rg.startContainer;
    if (!node || node.nodeType !== 3) return null;
    var host = node.parentElement;
    if (!host || host.closest(".text-lens")) return null;
    // the caret snaps to the nearest text, so confirm the point is really on it
    var probe = document.createRange();
    probe.selectNodeContents(node);
    var rects = probe.getClientRects(), hit = false;
    for (var i = 0; i < rects.length; i++) {
      var b = rects[i];
      if (x >= b.left - 2 && x <= b.right + 2 && y >= b.top - 2 && y <= b.bottom + 2) { hit = true; break; }
    }
    if (!hit) return null;
    return blockOf(host);
  }

  function paint() {
    raf = 0;

    var dx = px - sx, dy = py - sy;
    var moving = Math.abs(dx) + Math.abs(dy) > 0.35;
    if (moving) { sx += dx * EASE; sy += dy * EASE; } else { sx = px; sy = py; }

    var el = targetAt(sx, sy);
    var ok = el && hasText(el);
    var band = ok ? lineAt(el, sy) : null;
    if (band && hiddenByHeader(el, band)) band = null;
    var sameLine = lens && band && el === cacheEl && Math.abs(band.top - cacheTop) < 0.5;

    if (!lens) {
      if (!band || !acquire(el, band)) { running = false; return; }
      amp = 0; ampTarget = 1;
    } else if (sameLine) {
      ampTarget = 1;
    } else {
      /* Distance is measured across the line only, so without settling the old
         row first a new one would arrive already at full size. */
      ampTarget = 0;
      if (amp <= 0.02) {
        if (band && acquire(el, band)) { amp = 0; ampTarget = 1; }
        else { destroy(); running = false; return; }
      }
    }

    amp += (ampTarget - amp) * AMP_EASE;
    if (ampTarget === 0 && amp < 0.002) amp = 0;

    var list = chars;
    if (!list.length) { destroy(); running = false; return; }

    var fs = parseFloat(getComputedStyle(cacheEl).fontSize) || 16;
    var R = Math.max(45, WIDTH_CH * cacheAvgW);
    /* Plain exponential easing takes its biggest step on the first frame, which
       reads as a jolt when a row is picked up; smoothstep softens both ends. */
    var ampEased = amp * amp * (3 - 2 * amp);
    /* Small type is grown harder so the visible growth matches a headline's. */
    var A = Math.min(0.35, (ZOOM - 1) * (52 / Math.max(fs, 8))) * ampEased;

    var raw = new Array(list.length), fall = new Array(list.length);
    var extraSum = 0, weightSum = 0;
    for (var i = 0; i < list.length; i++) {
      var c = list[i];
      var d = Math.abs((c.x + c.w / 2) - sx);
      var t = d >= R ? 0 : 1 - d / R;
      var f = Math.pow(t, FALLOFF) * (3 - 2 * Math.min(t, 1));
      f = Math.max(0, Math.min(1, f));
      fall[i] = f;
      raw[i] = 1 + A * f;
      extraSum += c.w * (raw[i] - 1);
      weightSum += c.w * f * (1 - f);
    }

    /* A long line gives the borrowed width back across its middle, so both rims
       stay welded to the untouched text. A chip of three letters has nobody to
       borrow from: there, let it grow and centre the growth instead, which is
       the same thing a magnifier does to a word on its own. */
    if (weightSum > 0) {
      var k = -extraSum / weightSum;
      for (var j = 0; j < list.length; j++) raw[j] += k * fall[j] * (1 - fall[j]);
    }

    var run = 0, off = new Array(list.length);
    for (var m = 0; m < list.length; m++) {
      off[m] = run;
      run += list[m].w * (raw[m] - 1);
    }
    for (var m2 = 0; m2 < list.length; m2++) {
      spans[m2].style.transform =
        "translateX(" + off[m2].toFixed(2) + "px) scale(" + raw[m2].toFixed(4) + ")";
    }

    for (var q3 = 0; q3 < runs.length; q3++) {
      var rn = runs[q3], a = list[rn.from], z = list[rn.to];
      var l = a.x - lensLeft + off[rn.from] - rn.padL;
      var rgt = z.x - lensLeft + off[rn.to] + z.w * raw[rn.to] + rn.padR;
      rn.el.style.left = l.toFixed(2) + "px";
      rn.el.style.width = Math.max(0, rgt - l).toFixed(2) + "px";
    }

    if (moving || Math.abs(ampTarget - amp) > 0.004) {
      running = true;
      raf = requestAnimationFrame(paint);
    } else {
      running = false;
    }
  }

  function queue() {
    if (running) return;
    if (raf) cancelAnimationFrame(raf);
    raf = requestAnimationFrame(paint);
  }

  addEventListener("pointermove", function (e) {
    if (!lens) { sx = e.clientX; sy = e.clientY; }
    px = e.clientX; py = e.clientY;
    queue();
  }, { passive: true });

  addEventListener("scroll", destroy, { passive: true });
  addEventListener("blur", destroy);
  addEventListener("resize", destroy);
})();
