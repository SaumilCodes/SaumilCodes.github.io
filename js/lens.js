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

  var lens = null, spans = [], chars = [];
  var cacheEl = null, cacheTop = 0, cacheBottom = -1, cacheAvgW = 10;
  var raf = 0, px = 0, py = 0, sx = 0, sy = 0, running = false;
  var amp = 0, ampTarget = 1;

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
  function blockOf(el) {
    for (var n = el; n && n !== document.body; n = n.parentElement) {
      var d = getComputedStyle(n).display;
      if (d !== "inline" && d !== "inline-block" && d !== "inline-flex") return n;
    }
    return el;
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
    var all = rg.getClientRects(), best = null, bestD = Infinity;
    for (var i = 0; i < all.length; i++) {
      var b = all[i];
      if (b.width < 0.5 || b.height < 0.5) continue;
      if (y < b.top - 0.5 || y > b.bottom + 0.5) continue;
      var d = Math.abs((b.top + b.bottom) / 2 - y);
      if (d < bestD) { bestD = d; best = b; }
    }
    return best;
  }

  function charsOnLine(el, band) {
    var walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT, null);
    var out = [], n, r = document.createRange();
    while ((n = walker.nextNode())) {
      var t = n.nodeValue;
      for (var i = 0; i < t.length; i++) {
        r.setStart(n, i); r.setEnd(n, i + 1);
        var b = r.getBoundingClientRect();
        if (!b.width && !b.height) continue;
        var cy = b.top + b.height / 2;
        if (cy >= band.top && cy <= band.bottom) {
          out.push({ ch: t[i], x: b.left, y: b.top, w: b.width, h: b.height,
                     owner: n.parentElement || el });
        }
      }
    }
    return out;
  }

  function destroy() {
    if (lens) { lens.remove(); lens = null; }
    spans = []; chars = [];
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
    lens.style.left = minX + "px";
    lens.style.top = band.top + "px";
    /* Without an explicit size the box collapses, the background covers
       nothing, and the original shows through under the overlay: every glyph
       is drawn twice and the row reads as bold. The cover is the line box and
       never a pixel more, so the row above is left alone. */
    lens.style.width = (maxX - minX) + "px";
    lens.style.height = band.height + "px";
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
        fontFamily: d.fontFamily, fontWeight: d.fontWeight, fontStyle: d.fontStyle,
        fontSize: d.fontSize, fontVariationSettings: d.fontVariationSettings,
        fontFeatureSettings: d.fontFeatureSettings, letterSpacing: d.letterSpacing,
        wordSpacing: d.wordSpacing, color: d.color, textTransform: d.textTransform,
        textDecoration: d.textDecoration, textDecorationColor: d.textDecorationColor,
        textDecorationThickness: d.textDecorationThickness,
        textUnderlineOffset: d.textUnderlineOffset,
        background: d.backgroundColor
      };
      seen.set(node, own);
      return own;
    }

    /* A drop cap is a pseudo element, so its size and colour live nowhere in
       the character's own styles; lift them onto the first glyph by hand. */
    var firstLetter = null, firstIdx = -1;
    try {
      var fl = getComputedStyle(el, "::first-letter");
      if (fl && fl.fontSize && fl.fontSize !== cs.fontSize) {
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
      s.style.top = (c.y - band.top) + "px";
      s.style.height = c.h + "px";
      s.style.lineHeight = c.h + "px";
      for (var k in d) if (d[k]) s.style[k] = d[k];
      if (idx === firstIdx && firstLetter) {
        s.style.fontSize = firstLetter.fontSize;
        s.style.fontFamily = firstLetter.fontFamily;
        s.style.fontWeight = firstLetter.fontWeight;
        s.style.lineHeight = firstLetter.lineHeight;
        s.style.color = firstLetter.color;
      }
      lens.appendChild(s);
      return s;
    });
    document.body.appendChild(lens);
    chars = list;
  }

  function acquire(el, band) {
    var probe = charsOnLine(el, band);
    if (!probe.length) return false;
    var wsum = 0, wn = 0;
    for (var i = 0; i < probe.length; i++) if (probe[i].w > 0) { wsum += probe[i].w; wn++; }
    cacheAvgW = wn ? wsum / wn : 10;
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

  function paint() {
    raf = 0;

    var dx = px - sx, dy = py - sy;
    var moving = Math.abs(dx) + Math.abs(dy) > 0.35;
    if (moving) { sx += dx * EASE; sy += dy * EASE; } else { sx = px; sy = py; }

    var hit = document.elementFromPoint(sx, sy);
    var el = hit && !hit.closest(".text-lens") ? blockOf(hit) : null;
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

    /* Give the width back, weighted so it is zero at the cursor and zero at the
       rim: the peak keeps its magnification and the seam still closes. */
    if (weightSum > 0) {
      var k = -extraSum / weightSum;
      for (var j = 0; j < list.length; j++) raw[j] += k * fall[j] * (1 - fall[j]);
    }

    var run = 0;
    for (var m = 0; m < list.length; m++) {
      var sc = raw[m];
      spans[m].style.transform =
        "translateX(" + run.toFixed(2) + "px) scale(" + sc.toFixed(4) + ")";
      run += list[m].w * (sc - 1);
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
