/*! Gemini Watermark Remover | main.js
 *  Everything runs locally in the browser. Files are never uploaded. */
(function (root, factory) {
  var api = factory();
  if (typeof module === 'object' && module.exports) { module.exports = api.core; }
  else { api.start(); }
})(this, function () {
  'use strict';

  /* 
   * CORE: pure pixel logic (no DOM), so it can be tested in Node
   *  */
  var P = 0.7;                   // star exponent: <1 gives the concave "sparkle" sides
  var MAX_REGION = 3000000;      // largest area (px) filled in one go for images
  var MAX_VIDEO_REGION = 500000; // same limit for video frames

  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }

  function rng(seed) {
    var a = seed | 0;
    return function () {
      a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function inStar(u, v) { return u <= 1 && v <= 1 && Math.pow(u, P) + Math.pow(v, P) <= 1; }

  /* Sparkle size/position Gemini uses: 48px logo, 32px margin up to 1024px,
     96px logo, 64px margin on larger images. Scaled for small images. */
  function sparkleParams(W, H) {
    var base = (W > 1024 && H > 1024) ? 96 : Math.round(clamp(48 * Math.min(W, H) / 1024, 24, 48));
    return { base: base, margin: Math.round(base * 2 / 3) };
  }
  function defaultSparkleBox(W, H) {
    var p = sparkleParams(W, H);
    return { x: W - p.margin - p.base, y: H - p.margin - p.base, w: p.base, h: p.base };
  }
  function autoGrow(shape, size) {
    return shape === 'sparkle' ? Math.max(2, Math.round(size * 0.08)) : 2;
  }

  /* Binary dilation with a disc, touching only boundary pixels (cheap). */
  function dilate(src, dst, w, h, r) {
    dst.set(src);
    if (r <= 0) return;
    var offs = [], dy, dx, x, y, i, k;
    for (dy = -r; dy <= r; dy++) for (dx = -r; dx <= r; dx++) if (dx * dx + dy * dy <= r * r + 0.5) offs.push(dx, dy);
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) {
        i = y * w + x;
        if (!src[i]) continue;
        if (!((x > 0 && !src[i - 1]) || (x < w - 1 && !src[i + 1]) || (y > 0 && !src[i - w]) || (y < h - 1 && !src[i + w]) ||
              x === 0 || y === 0 || x === w - 1 || y === h - 1)) continue;
        for (k = 0; k < offs.length; k += 2) {
          var xx = x + offs[k], yy = y + offs[k + 1];
          if (xx >= 0 && xx < w && yy >= 0 && yy < h) dst[yy * w + xx] = 1;
        }
      }
    }
  }

  /* Region to read/write + hole mask (1 = pixel to rebuild) for a selection. */
  function buildRegion(sel, shape, grow, W, H) {
    var s = Math.min(sel.w, sel.h);
    var pad = grow + 14 + Math.round(s * 0.1) + (shape === 'sparkle' ? Math.ceil(s * 0.06) : 0);
    var x0 = Math.max(0, Math.floor(sel.x - pad)), y0 = Math.max(0, Math.floor(sel.y - pad));
    var x1 = Math.min(W, Math.ceil(sel.x + sel.w + pad)), y1 = Math.min(H, Math.ceil(sel.y + sel.h + pad));
    var rw = x1 - x0, rh = y1 - y0;
    if (rw < 2 || rh < 2) return null;
    var hole = new Uint8Array(rw * rh), x, y;
    if (shape === 'rect') {
      var hx0 = Math.max(x0, Math.floor(sel.x - grow)), hy0 = Math.max(y0, Math.floor(sel.y - grow));
      var hx1 = Math.min(x1, Math.ceil(sel.x + sel.w + grow)), hy1 = Math.min(y1, Math.ceil(sel.y + sel.h + grow));
      for (y = hy0; y < hy1; y++) for (x = hx0; x < hx1; x++) hole[(y - y0) * rw + (x - x0)] = 1;
    } else {
      var cx = sel.x + sel.w / 2, cy = sel.y + sel.h / 2, half = s / 2 * 1.08;
      var tmp = new Uint8Array(rw * rh);
      for (y = 0; y < rh; y++) {
        for (x = 0; x < rw; x++) {
          if (inStar(Math.abs(x0 + x + 0.5 - cx) / half, Math.abs(y0 + y + 0.5 - cy) / half)) tmp[y * rw + x] = 1;
        }
      }
      dilate(tmp, hole, rw, rh, grow);
    }
    return { x: x0, y: y0, w: rw, h: rh, hole: hole };
  }

  /*  Inpainter: pyramid push-pull + Laplace relaxation + grain  */
  function Inpainter(w, h, hole, opt) {
    opt = opt || {};
    this.w = w; this.h = h; this.hole = hole;
    this.iter = opt.iter == null ? 40 : opt.iter;
    this.noise = opt.noise == null ? 0.8 : opt.noise;
    var n = w * h, i, x, y, cnt = 0;
    for (i = 0; i < n; i++) if (hole[i]) cnt++;
    var idx = new Int32Array(cnt); cnt = 0;
    for (i = 0; i < n; i++) if (hole[i]) idx[cnt++] = i;
    this.idx = idx;

    var lv = [], lw = w, lh = h;
    for (;;) {
      var m = lw * lh;
      lv.push({ w: lw, h: lh, r: new Float32Array(m), g: new Float32Array(m), b: new Float32Array(m), k: new Float32Array(m) });
      if ((lw <= 2 && lh <= 2) || lv.length >= 16) break;
      lw = (lw + 1) >> 1; lh = (lh + 1) >> 1;
    }
    this.lv = lv;

    // ring of known pixels around the hole, used to measure the image grain
    var near = new Uint8Array(n), R = 7;
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) {
        i = y * w + x;
        if (!hole[i]) continue;
        if (!((x > 0 && !hole[i - 1]) || (x < w - 1 && !hole[i + 1]) || (y > 0 && !hole[i - w]) || (y < h - 1 && !hole[i + w]))) continue;
        for (var yy = Math.max(0, y - R); yy <= Math.min(h - 1, y + R); yy++) {
          for (var xx = Math.max(0, x - R); xx <= Math.min(w - 1, x + R); xx++) near[yy * w + xx] = 1;
        }
      }
    }
    var ring = [];
    for (y = 1; y < h - 1; y++) {
      for (x = 1; x < w - 1; x++) {
        i = y * w + x;
        if (hole[i] || !near[i]) continue;
        if (hole[i - 1] || hole[i + 1] || hole[i - w] || hole[i + w] || hole[i - w - 1] || hole[i - w + 1] || hole[i + w - 1] || hole[i + w + 1]) continue;
        ring.push(i);
      }
    }
    this.ring = Int32Array.from(ring);
  }

  /* px: RGBA bytes of the region (w*h*4). Hole pixels are rewritten in place. */
  Inpainter.prototype.run = function (px, seed) {
    var w = this.w, h = this.h, n = w * h, hole = this.hole, L = this.lv;
    var i, j, k, x, y, ci, pi, c = L[0];
    for (i = 0, j = 0; i < n; i++, j += 4) {
      if (hole[i]) { c.r[i] = 0; c.g[i] = 0; c.b[i] = 0; c.k[i] = 0; }
      else { c.r[i] = px[j]; c.g[i] = px[j + 1]; c.b[i] = px[j + 2]; c.k[i] = 1; }
    }
    // pull: sum known pixels up the pyramid
    for (k = 0; k < L.length - 1; k++) {
      var a = L[k], b = L[k + 1];
      b.r.fill(0); b.g.fill(0); b.b.fill(0); b.k.fill(0);
      for (y = 0; y < a.h; y++) {
        var row = y * a.w, prow = (y >> 1) * b.w;
        for (x = 0; x < a.w; x++) {
          ci = row + x; pi = prow + (x >> 1);
          b.r[pi] += a.r[ci]; b.g[pi] += a.g[ci]; b.b[pi] += a.b[ci]; b.k[pi] += a.k[ci];
        }
      }
    }
    // push: average where known, bilinear from the coarser level where not
    var top = L[L.length - 1];
    for (i = 0; i < top.k.length; i++) {
      if (top.k[i] > 0) { top.r[i] /= top.k[i]; top.g[i] /= top.k[i]; top.b[i] /= top.k[i]; }
      else { top.r[i] = 128; top.g[i] = 128; top.b[i] = 128; }
    }
    for (k = L.length - 2; k >= 0; k--) {
      var cc = L[k], pp = L[k + 1];
      for (y = 0; y < cc.h; y++) {
        for (x = 0; x < cc.w; x++) {
          ci = y * cc.w + x;
          var kk = cc.k[ci];
          if (kk > 0) { cc.r[ci] /= kk; cc.g[ci] /= kk; cc.b[ci] /= kk; continue; }
          var fx = (x + 0.5) * 0.5 - 0.5, fy = (y + 0.5) * 0.5 - 0.5;
          var x0 = Math.floor(fx), y0 = Math.floor(fy), tx = fx - x0, ty = fy - y0;
          var xa = clamp(x0, 0, pp.w - 1), xb = clamp(x0 + 1, 0, pp.w - 1);
          var ya = clamp(y0, 0, pp.h - 1), yb = clamp(y0 + 1, 0, pp.h - 1);
          var i00 = ya * pp.w + xa, i10 = ya * pp.w + xb, i01 = yb * pp.w + xa, i11 = yb * pp.w + xb;
          var w00 = (1 - tx) * (1 - ty), w10 = tx * (1 - ty), w01 = (1 - tx) * ty, w11 = tx * ty;
          cc.r[ci] = pp.r[i00] * w00 + pp.r[i10] * w10 + pp.r[i01] * w01 + pp.r[i11] * w11;
          cc.g[ci] = pp.g[i00] * w00 + pp.g[i10] * w10 + pp.g[i01] * w01 + pp.g[i11] * w11;
          cc.b[ci] = pp.b[i00] * w00 + pp.b[i10] * w10 + pp.b[i01] * w01 + pp.b[i11] * w11;
        }
      }
    }
    // relax toward a smooth (harmonic) surface so edges meet the surroundings
    var idx = this.idx, m = idx.length, R = c.r, G = c.g, B = c.b, it, t, ii, yy2, xx2, l, rr, u, d, om = 1.6;
    for (it = 0; it < this.iter; it++) {
      for (t = 0; t < m; t++) {
        ii = (it & 1) ? idx[m - 1 - t] : idx[t];
        yy2 = (ii / w) | 0; xx2 = ii - yy2 * w;
        l = xx2 > 0 ? ii - 1 : ii; rr = xx2 < w - 1 ? ii + 1 : ii;
        u = yy2 > 0 ? ii - w : ii; d = yy2 < h - 1 ? ii + w : ii;
        R[ii] += om * ((R[l] + R[rr] + R[u] + R[d]) * 0.25 - R[ii]);
        G[ii] += om * ((G[l] + G[rr] + G[u] + G[d]) * 0.25 - G[ii]);
        B[ii] += om * ((B[l] + B[rr] + B[u] + B[d]) * 0.25 - B[ii]);
      }
    }
    // measure grain around the hole and add a little back so the patch is not too clean
    var ring = this.ring, rc = ring.length, sr = 0, sg = 0, sb = 0, w4 = w * 4, v, m8;
    for (t = 0; t < rc; t++) {
      j = ring[t] * 4;
      m8 = (px[j - 4] + px[j + 4] + px[j - w4] + px[j + w4] + px[j - w4 - 4] + px[j - w4 + 4] + px[j + w4 - 4] + px[j + w4 + 4]) / 8; v = px[j] - m8; sr += v * v;
      m8 = (px[j - 3] + px[j + 5] + px[j - w4 + 1] + px[j + w4 + 1] + px[j - w4 - 3] + px[j - w4 + 5] + px[j + w4 - 3] + px[j + w4 + 5]) / 8; v = px[j + 1] - m8; sg += v * v;
      m8 = (px[j - 2] + px[j + 6] + px[j - w4 + 2] + px[j + w4 + 2] + px[j - w4 - 2] + px[j - w4 + 6] + px[j + w4 - 2] + px[j + w4 + 6]) / 8; v = px[j + 2] - m8; sb += v * v;
    }
    var k2 = rc ? this.noise / 1.06 : 0;
    var dr = rc ? Math.min(6, Math.sqrt(sr / rc)) * k2 : 0;
    var dg = rc ? Math.min(6, Math.sqrt(sg / rc)) * k2 : 0;
    var db = rc ? Math.min(6, Math.sqrt(sb / rc)) * k2 : 0;
    var rand = rng(seed || 1), common, nz = dr + dg + db > 0.01;
    for (t = 0; t < m; t++) {
      ii = idx[t]; j = ii * 4;
      if (nz) {
        common = (rand() + rand() + rand() - 1.5) * 1.6;
        px[j] = R[ii] + (common + (rand() + rand() + rand() - 1.5) * 1.2) * dr;
        px[j + 1] = G[ii] + (common + (rand() + rand() + rand() - 1.5) * 1.2) * dg;
        px[j + 2] = B[ii] + (common + (rand() + rand() + rand() - 1.5) * 1.2) * db;
      } else { px[j] = R[ii]; px[j + 1] = G[ii]; px[j + 2] = B[ii]; }
      px[j + 3] = 255;
    }
  };

  /*  Sparkle detection: star-shaped template match  */
  function detectWindow(W, H) {
    if (W < 120 || H < 120) return null;
    var p = sparkleParams(W, H), R = Math.round(p.base * 0.6), maxS = Math.ceil(p.base * 1.45);
    var cx0 = W - p.margin - p.base / 2, cy0 = H - p.margin - p.base / 2;
    var x0 = Math.max(0, Math.floor(cx0 - R - maxS * 0.85)), y0 = Math.max(0, Math.floor(cy0 - R - maxS * 0.85));
    return { x: x0, y: y0, w: W - x0, h: H - y0, base: p.base, cx0: cx0, cy0: cy0, R: R };
  }

  function makeTemplate(s) {
    var stride = Math.max(1, Math.round(s / 48)), half = s / 2, ext = Math.ceil(half * 1.65);
    var ins = [], outs = [], dx, dy;
    for (dy = -ext; dy <= ext; dy += stride) {
      for (dx = -ext; dx <= ext; dx += stride) {
        var u = Math.abs(dx) / half, v = Math.abs(dy) / half;
        var t = Math.pow(u, P) + Math.pow(v, P);
        if (u <= 1 && v <= 1 && t <= 0.8) ins.push(dx, dy);
        else if (t >= 1.3 && Math.max(u, v) <= 1.6) outs.push(dx, dy);
      }
    }
    return { s: s, ins: ins, outs: outs, half: half };
  }

  /* crop: {data,width,height} of the detection window (RGBA). Returns {found, box, diff, frac}. */
  function detectSparkle(crop, win) {
    var cw = crop.width, ch = crop.height, d = crop.data, luma = new Float32Array(cw * ch), i;
    for (i = 0; i < cw * ch; i++) luma[i] = 0.299 * d[i * 4] + 0.587 * d[i * 4 + 1] + 0.114 * d[i * 4 + 2];

    // brightness of the star core minus the surroundings, and how much of the core is brighter
    function evalAt(tpl, cx, cy) {
      var lx = cx - win.x, ly = cy - win.y, half = tpl.half, ins = tpl.ins, outs = tpl.outs;
      if (lx - half < 0 || ly - half < 0 || lx + half >= cw || ly + half >= ch) return null;
      var k, x, y, so = 0, no = 0, si = 0, ni = ins.length / 2, bright = 0;
      for (k = 0; k < outs.length; k += 2) {
        x = lx + outs[k]; y = ly + outs[k + 1];
        if (x < 0 || y < 0 || x >= cw || y >= ch) continue;
        so += luma[y * cw + x]; no++;
      }
      if (no < 80 || ni < 20) return null;
      var mo = so / no;
      for (k = 0; k < ins.length; k += 2) {
        var v = luma[(ly + ins[k + 1]) * cw + lx + ins[k]];
        si += v; if (v > mo + 3) bright++;
      }
      var diff = si / ni - mo, frac = bright / ni;
      return (diff >= 8 && frac >= 0.85) ? { score: diff * frac, diff: diff, frac: frac, mo: mo } : null;
    }

    var base = win.base, st = base >= 96 ? 2 : 1, factors = [0.7, 0.85, 1, 1.2, 1.45];
    var best = null, cx, cy, f, e;
    for (f = 0; f < factors.length; f++) {
      var tpl = makeTemplate(Math.round(base * factors[f]));
      for (cy = Math.round(win.cy0 - win.R); cy <= win.cy0 + win.R; cy += st) {
        for (cx = Math.round(win.cx0 - win.R); cx <= win.cx0 + win.R; cx += st) {
          e = evalAt(tpl, cx, cy);
          if (e && (!best || e.score > best.score)) best = { score: e.score, diff: e.diff, frac: e.frac, mo: e.mo, cx: cx, cy: cy, s: tpl.s };
        }
      }
    }
    if (!best) return { found: false };
    // refine the position at 1px steps around the coarse hit
    var ref = best, ds, dx, dy;
    for (ds = -4; ds <= 4; ds += 2) {
      var t2 = makeTemplate(Math.max(12, best.s + ds));
      for (dy = -3; dy <= 3; dy++) {
        for (dx = -3; dx <= 3; dx++) {
          e = evalAt(t2, best.cx + dx, best.cy + dy);
          if (e && e.score > ref.score) ref = { score: e.score, diff: e.diff, frac: e.frac, mo: e.mo, cx: best.cx + dx, cy: best.cy + dy, s: t2.s };
        }
      }
    }
    // the score plateau is flat inside the star, so pin the centre with the centroid of the bright pixels
    var ccx = ref.cx + 0.5, ccy = ref.cy + 0.5, it, thr = ref.mo + ref.diff * 0.45, rad = Math.ceil(ref.s * 0.75);
    for (it = 0; it < 3; it++) {
      var sx = 0, sy = 0, sn = 0, yy, xx;
      for (yy = Math.floor(ccy - rad); yy <= Math.ceil(ccy + rad); yy++) {
        for (xx = Math.floor(ccx - rad); xx <= Math.ceil(ccx + rad); xx++) {
          var lx2 = xx - win.x, ly2 = yy - win.y;
          if (lx2 < 0 || ly2 < 0 || lx2 >= cw || ly2 >= ch) continue;
          if (luma[ly2 * cw + lx2] > thr) { sx += xx + 0.5; sy += yy + 0.5; sn++; }
        }
      }
      if (sn < 20) break;
      ccx = sx / sn; ccy = sy / sn;
    }
    // a real logo has a sharp edge; a soft bright patch in a photo does not. Look along the diagonals.
    var prof = [], r, q;
    for (r = 1; r <= Math.ceil(ref.s * 0.62) + 3; r++) {
      var a = 0, an = 0, o = r * 0.7071;
      for (q = 0; q < 4; q++) {
        var px2 = Math.floor(ccx + (q & 1 ? o : -o)) - win.x, py2 = Math.floor(ccy + (q & 2 ? o : -o)) - win.y;
        if (px2 >= 0 && py2 >= 0 && px2 < cw && py2 < ch) { a += luma[py2 * cw + px2]; an++; }
      }
      prof.push(an ? a / an : NaN);
    }
    var step = 0;
    for (r = 0; r + 3 < prof.length; r++) if (prof[r] - prof[r + 3] > step) step = prof[r] - prof[r + 3];
    if (!(step >= Math.max(5, ref.diff * 0.45))) return { found: false };
    // the size is a fuzzy estimate; Gemini uses fixed sizes, so never go much smaller than expected
    var s = Math.max(ref.s, Math.round(base * 0.95));
    return { found: true, diff: ref.diff, frac: ref.frac, box: { x: Math.round(ccx - s / 2), y: Math.round(ccy - s / 2), w: s, h: s } };
  }

  var core = {
    Inpainter: Inpainter, buildRegion: buildRegion, detectWindow: detectWindow, detectSparkle: detectSparkle,
    defaultSparkleBox: defaultSparkleBox, autoGrow: autoGrow, inStar: inStar, sparkleParams: sparkleParams,
    MAX_REGION: MAX_REGION, MAX_VIDEO_REGION: MAX_VIDEO_REGION
  };

  /* 
   * UI
   *  */
  function start() {
    var $ = function (id) { return document.getElementById(id); };
    var raf = window.requestAnimationFrame.bind(window);
    var later = function (fn) { raf(function () { setTimeout(fn, 0); }); };

    function setStatus(el, text, kind) {
      el.textContent = text || '';
      el.className = 'status' + (kind ? ' ' + kind : '');
    }
    function saveBlob(blob, filename) {
      var a = document.createElement('a');
      a.href = URL.createObjectURL(blob); a.download = filename;
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(function () { URL.revokeObjectURL(a.href); }, 5000);
    }
    function baseName(name, fallback) { return (name || '').replace(/\.[^.]+$/, '').replace(/[^\w\- ]+/g, '').trim() || fallback; }
    function fmtTime(t) {
      if (!isFinite(t)) t = 0;
      var m = Math.floor(t / 60), s = Math.floor(t % 60);
      return m + ':' + (s < 10 ? '0' : '') + s;
    }

    /*  selection box (drag, move, resize) shared by image + video  */
    function attachSelector(o) {
      var mode = null, h = null, start = null, orig = null, moved = false;
      function pt(e) {
        var r = o.surface.getBoundingClientRect(), d = o.dims();
        return { x: (e.clientX - r.left) * d.W / r.width, y: (e.clientY - r.top) * d.H / r.height, k: d.W / r.width, W: d.W, H: d.H };
      }
      function place() {
        var s = o.get(), d = o.dims(), el = o.el;
        o.surface.classList.toggle('free', !s);
        if (!s) { el.hidden = true; return; }
        el.hidden = false;
        el.style.left = (s.x / d.W * 100) + '%'; el.style.top = (s.y / d.H * 100) + '%';
        el.style.width = (s.w / d.W * 100) + '%'; el.style.height = (s.h / d.H * 100) + '%';
        el.classList.toggle('tiny', el.parentNode.clientWidth * s.w / d.W < 60);
      }
      function rectFrom(ax, ay, bx, by, p) {
        var x0 = Math.min(ax, bx), y0 = Math.min(ay, by), w = Math.abs(bx - ax), hh = Math.abs(by - ay);
        if (o.square()) { var m = Math.max(w, hh); w = hh = m; if (bx < ax) x0 = ax - m; if (by < ay) y0 = ay - m; }
        x0 = clamp(x0, 0, p.W - 1); y0 = clamp(y0, 0, p.H - 1);
        return { x: x0, y: y0, w: Math.max(2, Math.min(w, p.W - x0)), h: Math.max(2, Math.min(hh, p.H - y0)) };
      }
      o.surface.addEventListener('pointerdown', function (e) {
        if (o.locked() || (e.button != null && e.button !== 0)) return;
        var p = pt(e), s = o.get(), grab = 16 * p.k;
        mode = 'new'; h = null; moved = false;
        if (s) {
          var cs = { nw: [s.x, s.y], ne: [s.x + s.w, s.y], sw: [s.x, s.y + s.h], se: [s.x + s.w, s.y + s.h] };
          for (var key in cs) { if (Math.hypot(p.x - cs[key][0], p.y - cs[key][1]) <= grab) { mode = 'resize'; h = key; break; } }
          if (mode === 'new' && p.x >= s.x && p.x <= s.x + s.w && p.y >= s.y && p.y <= s.y + s.h) mode = 'move';
        }
        start = p; orig = s ? { x: s.x, y: s.y, w: s.w, h: s.h } : null;
        try { o.surface.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
        e.preventDefault();
      });
      o.surface.addEventListener('pointermove', function (e) {
        if (!mode) return;
        var p = pt(e), dx = p.x - start.x, dy = p.y - start.y;
        if (Math.abs(dx) + Math.abs(dy) > 2 * p.k) moved = true;
        if (!moved) return;
        if (mode === 'new') o.set(rectFrom(start.x, start.y, p.x, p.y, p));
        else if (mode === 'move') {
          o.set({ x: clamp(orig.x + dx, 0, p.W - orig.w), y: clamp(orig.y + dy, 0, p.H - orig.h), w: orig.w, h: orig.h });
        } else {
          var fx = (h === 'nw' || h === 'sw') ? orig.x + orig.w : orig.x;
          var fy = (h === 'nw' || h === 'ne') ? orig.y + orig.h : orig.y;
          o.set(rectFrom(fx, fy, clamp(p.x, 0, p.W), clamp(p.y, 0, p.H), p));
        }
        place();
      });
      function end() {
        if (!mode) return;
        var wasMoved = moved; mode = null;
        if (wasMoved) o.onEnd();
      }
      o.surface.addEventListener('pointerup', end);
      o.surface.addEventListener('pointercancel', end);
      // keyboard nudging for accessibility
      var timer = null;
      o.el.addEventListener('keydown', function (e) {
        var s = o.get(); if (!s || o.locked()) return;
        var step = e.shiftKey ? 10 : 1, d = o.dims(), dx = 0, dy = 0;
        if (e.key === 'ArrowLeft') dx = -step; else if (e.key === 'ArrowRight') dx = step;
        else if (e.key === 'ArrowUp') dy = -step; else if (e.key === 'ArrowDown') dy = step; else return;
        e.preventDefault();
        o.set({ x: clamp(s.x + dx, 0, d.W - s.w), y: clamp(s.y + dy, 0, d.H - s.h), w: s.w, h: s.h });
        place();
        clearTimeout(timer); timer = setTimeout(o.onEnd, 350);
      });
      return { place: place };
    }

    function holdButton(btn, down, up) {
      var on = false;
      function d() { if (!on) { on = true; btn.setAttribute('aria-pressed', 'true'); down(); } }
      function u() { if (on) { on = false; btn.setAttribute('aria-pressed', 'false'); up(); } }
      btn.addEventListener('pointerdown', function (e) { e.preventDefault(); d(); });
      ['pointerup', 'pointerleave', 'pointercancel', 'blur'].forEach(function (n) { btn.addEventListener(n, u); });
      btn.addEventListener('keydown', function (e) { if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); d(); } });
      btn.addEventListener('keyup', function (e) { if (e.key === ' ' || e.key === 'Enter') u(); });
    }

    /* ====================== IMAGE ====================== */
    function initImage() {
      var el = {
        drop: $('imgDrop'), input: $('imgInput'), work: $('imgWork'), stage: $('imgStage'), canvas: $('imgCanvas'),
        sel: $('imgSel'), status: $('imgStatus'), grow: $('imgGrow'), growVal: $('imgGrowVal'), detect: $('imgDetect'),
        compare: $('imgCompare'), more: $('imgMore'), fmt: $('imgFormat'), dl: $('imgDownload'), reset: $('imgReset')
      };
      var ctx = el.canvas.getContext('2d', { willReadFrequently: true });
      var I = { W: 0, H: 0, sel: null, shape: 'sparkle', grow: 4, prev: null, name: 'image', type: 'image/png', busy: false };

      function shape() { return document.querySelector('input[name="imgShape"]:checked').value; }
      function restore() { if (I.prev) { ctx.putImageData(I.prev.orig, I.prev.x, I.prev.y); I.prev = null; } }

      function apply(msg) {
        restore();
        if (!I.sel) return;
        I.shape = shape();
        var r = buildRegion(I.sel, I.shape, I.grow, I.W, I.H);
        if (!r) return;
        if (r.w * r.h > MAX_REGION) { setStatus(el.status, 'That area is too large. Draw a smaller box around the logo.', 'warn'); return; }
        var orig = ctx.getImageData(r.x, r.y, r.w, r.h);
        var out = new ImageData(new Uint8ClampedArray(orig.data), r.w, r.h);
        new Inpainter(r.w, r.h, r.hole, { iter: 80, noise: 0.85 }).run(out.data, 20260);
        ctx.putImageData(out, r.x, r.y);
        I.prev = { x: r.x, y: r.y, orig: orig, out: out };
        setStatus(el.status, msg || 'Done. Hold the Compare button to see the original, or nudge the box if you can still see traces.', 'ok');
      }

      function showSel() { selector.place(); }

      function runDetect(auto) {
        restore();
        var win = detectWindow(I.W, I.H), res = null;
        if (win) res = detectSparkle(ctx.getImageData(win.x, win.y, win.w, win.h), win);
        if (res && res.found) {
          I.sel = res.box; el.grow.value = I.grow = autoGrow(I.shape, res.box.w); el.growVal.textContent = I.grow + ' px';
          showSel();
          apply('Found the sparkle in the bottom-right corner and removed it. Hold Compare to check the original.');
        } else {
          I.sel = defaultSparkleBox(I.W, I.H); el.grow.value = I.grow = autoGrow(I.shape, I.sel.w); el.growVal.textContent = I.grow + ' px';
          showSel();
          setStatus(el.status, (auto ? 'Could not spot the sparkle automatically. ' : 'No sparkle found here. ') +
            'Drag the box over the logo (or draw a new one) and release to remove it.', 'warn');
        }
      }

      var selector = attachSelector({
        surface: el.stage, el: el.sel,
        dims: function () { return { W: I.W, H: I.H }; },
        get: function () { return I.sel; }, set: function (s) { I.sel = s; },
        square: function () { return shape() === 'sparkle'; },
        locked: function () { return I.busy; },
        onEnd: function () { setStatus(el.status, 'Working…'); later(function () { apply(); }); }
      });

      function decode(file) {
        return createImageBitmap(file).catch(function () {
          return new Promise(function (res, rej) {
            var u = URL.createObjectURL(file), im = new Image();
            im.onload = function () { URL.revokeObjectURL(u); res(im); };
            im.onerror = function () { URL.revokeObjectURL(u); rej(new Error('decode')); };
            im.src = u;
          });
        });
      }

      function load(file) {
        setStatus(el.status, 'Opening image…');
        el.work.hidden = false; el.drop.hidden = true;
        decode(file).then(function (bmp) {
          var w = bmp.width || bmp.naturalWidth, h = bmp.height || bmp.naturalHeight, k = Math.min(1, 8192 / Math.max(w, h), Math.sqrt(16000000 / (w * h)));
          I.W = Math.round(w * k); I.H = Math.round(h * k);
          el.canvas.width = I.W; el.canvas.height = I.H;
          ctx.drawImage(bmp, 0, 0, I.W, I.H);
          if (bmp.close) bmp.close();
          el.stage.style.setProperty('--ar', I.W / I.H);
          I.prev = null; I.name = baseName(file.name, 'image'); I.type = file.type;
          el.fmt.value = file.type === 'image/jpeg' ? 'image/jpeg' : file.type === 'image/webp' ? 'image/webp' : 'image/png';
          document.querySelector('input[name="imgShape"][value="sparkle"]').checked = true;
          I.shape = 'sparkle';
          later(function () { runDetect(true); });
        }).catch(function () {
          el.work.hidden = true; el.drop.hidden = false;
          setStatus($('imgDropStatus'), 'Could not open that file. Please choose a PNG, JPG or WebP image.', 'err');
        });
      }

      el.input.addEventListener('change', function () { if (el.input.files[0]) load(el.input.files[0]); el.input.value = ''; });
      el.grow.addEventListener('input', function () { el.growVal.textContent = el.grow.value + ' px'; });
      el.grow.addEventListener('change', function () { I.grow = +el.grow.value; apply(); });
      Array.prototype.forEach.call(document.querySelectorAll('input[name="imgShape"]'), function (r) {
        r.addEventListener('change', function () {
          I.shape = shape();
          if (I.sel && I.shape === 'sparkle') { var s = Math.max(I.sel.w, I.sel.h); I.sel = { x: I.sel.x, y: I.sel.y, w: Math.min(s, I.W - I.sel.x), h: Math.min(s, I.H - I.sel.y) }; showSel(); }
          apply();
        });
      });
      el.detect.addEventListener('click', function () { setStatus(el.status, 'Looking for the sparkle…'); later(function () { runDetect(false); }); });
      el.more.addEventListener('click', function () {
        I.prev = null; I.sel = null; showSel();
        setStatus(el.status, 'Draw a box around the next mark you want to remove.', '');
      });
      holdButton(el.compare,
        function () { if (I.prev) ctx.putImageData(I.prev.orig, I.prev.x, I.prev.y); },
        function () { if (I.prev) ctx.putImageData(I.prev.out, I.prev.x, I.prev.y); });
      el.reset.addEventListener('click', function () {
        I.prev = null; I.sel = null; el.work.hidden = true; el.drop.hidden = false; setStatus($('imgDropStatus'), '');
      });
      el.dl.addEventListener('click', function () {
        var type = el.fmt.value, c = el.canvas;
        if (type === 'image/jpeg') {
          c = document.createElement('canvas'); c.width = I.W; c.height = I.H;
          var x = c.getContext('2d'); x.fillStyle = '#fff'; x.fillRect(0, 0, I.W, I.H); x.drawImage(el.canvas, 0, 0);
        }
        c.toBlob(function (b) {
          if (!b) { setStatus(el.status, 'Could not create the file. Try another format.', 'err'); return; }
          var ext = b.type === 'image/jpeg' ? 'jpg' : b.type === 'image/webp' ? 'webp' : 'png';
          saveBlob(b, I.name + '-no-watermark.' + ext);
        }, type, 0.95);
      });

      return { load: load };
    }

    /* ====================== VIDEO ====================== */
    function initVideo() {
      var el = {
        drop: $('vidDrop'), input: $('vidInput'), work: $('vidWork'), stage: $('vidStage'), canvas: $('vidCanvas'), sel: $('vidSel'),
        status: $('vidStatus'), grow: $('vidGrow'), growVal: $('vidGrowVal'), play: $('vidPlay'), seek: $('vidSeek'), time: $('vidTime'),
        compare: $('vidCompare'), go: $('vidExport'), cancel: $('vidCancel'), prog: $('vidProgress'), progWrap: $('vidProgressWrap'),
        result: $('vidResult'), resultVideo: $('vidResultPlayer'), dl: $('vidDownload'), reset: $('vidReset')
      };
      var ctx = el.canvas.getContext('2d', { willReadFrequently: true });
      var V = { video: null, url: null, W: 0, H: 0, sel: null, grow: 2, inp: null, region: null, playing: false, busy: false,
        compare: false, seed: 7, loop: 0, name: 'video', ac: null, src: null, dest: null, cancel: false, endHook: null, resultUrl: null };

      function shape() { return document.querySelector('input[name="vidShape"]:checked').value; }

      function draw() {
        if (!V.video) return;
        try { ctx.drawImage(V.video, 0, 0, V.W, V.H); } catch (e) { return; }
        if (V.inp && !V.compare) {
          var r = V.region, id = ctx.getImageData(r.x, r.y, r.w, r.h);
          V.seed = (Math.imul(V.seed, 1664525) + 1013904223) | 0;
          V.inp.run(id.data, V.seed);
          ctx.putImageData(id, r.x, r.y);
        }
      }
      function rebuild() {
        V.inp = null; V.region = null;
        if (V.sel) {
          var r = buildRegion(V.sel, shape(), V.grow, V.W, V.H);
          if (r && r.w * r.h > MAX_VIDEO_REGION) setStatus(el.status, 'That area is too large for video. Draw a smaller box around the logo.', 'warn');
          else if (r) { V.region = r; V.inp = new Inpainter(r.w, r.h, r.hole, { iter: 10, noise: 0.55 }); }
        }
        draw();
      }
      function loop() {
        var id = ++V.loop;
        (function step() {
          if (!V.playing || id !== V.loop) return;
          draw();
          if (V.video.requestVideoFrameCallback) V.video.requestVideoFrameCallback(step); else raf(step);
        })();
      }
      function updateTime() {
        var v = V.video; if (!v) return;
        el.time.textContent = fmtTime(v.currentTime) + ' / ' + fmtTime(v.duration);
        if (!el.seek.matches(':active')) el.seek.value = v.duration ? Math.round(v.currentTime / v.duration * 1000) : 0;
        if (V.busy && v.duration) el.prog.value = v.currentTime / v.duration;
      }
      function lock(on) {
        V.busy = on;
        el.go.disabled = on; el.reset.disabled = on; el.play.disabled = on; el.seek.disabled = on; el.grow.disabled = on;
        el.cancel.hidden = !on; el.progWrap.hidden = !on;
        Array.prototype.forEach.call(document.querySelectorAll('input[name="vidShape"]'), function (r) { r.disabled = on; });
      }
      function teardown() {
        V.loop++; V.playing = false;
        if (V.video) { V.video.pause(); V.video.remove(); }
        if (V.url) URL.revokeObjectURL(V.url);
        if (V.resultUrl) URL.revokeObjectURL(V.resultUrl);
        if (V.ac) { try { V.ac.close(); } catch (e) { /* ignore */ } }
        V.video = null; V.url = null; V.resultUrl = null; V.ac = null; V.src = null; V.dest = null; V.inp = null; V.region = null;
        el.result.hidden = true; el.resultVideo.removeAttribute('src');
      }

      var selector = attachSelector({
        surface: el.stage, el: el.sel,
        dims: function () { return { W: V.W, H: V.H }; },
        get: function () { return V.sel; }, set: function (s) { V.sel = s; },
        square: function () { return shape() === 'sparkle'; },
        locked: function () { return V.busy; },
        onEnd: function () { rebuild(); setStatus(el.status, 'Box updated. Press play to preview the result.', ''); }
      });

      function load(file) {
        teardown();
        el.drop.hidden = true; el.work.hidden = false;
        setStatus(el.status, 'Opening video…');
        var v = document.createElement('video');
        v.playsInline = true; v.preload = 'auto'; v.setAttribute('aria-hidden', 'true'); v.tabIndex = -1;
        V.video = v; V.url = URL.createObjectURL(file); V.name = baseName(file.name, 'video');
        el.stage.insertBefore(v, el.canvas);
        v.addEventListener('error', function () {
          teardown(); el.work.hidden = true; el.drop.hidden = false;
          setStatus($('vidDropStatus'), 'Could not open that video. Try an MP4 or WebM file.', 'err');
        });
        v.addEventListener('loadeddata', function () {
          if (!v.videoWidth) { v.dispatchEvent(new Event('error')); return; }
          var k = Math.min(1, 1920 / Math.max(v.videoWidth, v.videoHeight));
          V.W = Math.max(2, Math.round(v.videoWidth * k / 2) * 2); V.H = Math.max(2, Math.round(v.videoHeight * k / 2) * 2);
          el.canvas.width = V.W; el.canvas.height = V.H;
          el.stage.style.setProperty('--ar', V.W / V.H);
          var bw = Math.round(V.W * 0.13), bh = Math.round(V.H * 0.075);
          V.sel = { x: V.W - Math.round(V.W * 0.025) - bw, y: V.H - Math.round(V.H * 0.035) - bh, w: bw, h: bh };
          document.querySelector('input[name="vidShape"][value="rect"]').checked = true;
          V.grow = 2; el.grow.value = 2; el.growVal.textContent = '2 px';
          el.play.textContent = 'Play'; el.play.setAttribute('aria-label', 'Play preview');
          selector.place(); rebuild(); updateTime();
          setStatus(el.status, 'Move or resize the box so it covers the logo, then press play to preview. When it looks right, save the video.', '');
        }, { once: true });
        v.addEventListener('seeked', function () { if (!V.playing) draw(); updateTime(); });
        v.addEventListener('timeupdate', updateTime);
        v.addEventListener('play', function () { V.playing = true; el.play.textContent = 'Pause'; el.play.setAttribute('aria-label', 'Pause preview'); loop(); });
        v.addEventListener('pause', function () { V.playing = false; el.play.textContent = 'Play'; el.play.setAttribute('aria-label', 'Play preview'); draw(); });
        v.src = V.url;
      }

      function seekTo(t) {
        return new Promise(function (res) {
          var v = V.video;
          if (Math.abs(v.currentTime - t) < 0.001) { res(); return; }
          var h = function () { v.removeEventListener('seeked', h); res(); };
          v.addEventListener('seeked', h); v.currentTime = t;
        });
      }
      function pickMime() {
        // only accept MP4 when it really is H.264 + AAC, otherwise the file would not play everywhere
        var list = ['video/mp4;codecs=avc1.640028,mp4a.40.2', 'video/mp4;codecs=avc1.42E01E,mp4a.40.2', 'video/mp4;codecs=avc1,mp4a.40.2',
          'video/webm;codecs=vp9,opus', 'video/webm;codecs=vp8,opus', 'video/webm'];
        for (var i = 0; i < list.length; i++) if (MediaRecorder.isTypeSupported(list[i])) return list[i];
        return '';
      }

      function exportVideo() {
        if (!window.MediaRecorder || !el.canvas.captureStream) {
          setStatus(el.status, 'This browser cannot record video. Please try a recent Chrome, Edge, Firefox or Safari.', 'err'); return;
        }
        if (!V.sel || !V.inp) { setStatus(el.status, 'Place the box over the logo first.', 'warn'); return; }
        lock(true); V.cancel = false; V.compare = false;
        el.result.hidden = true; el.prog.value = 0;
        setStatus(el.status, 'Processing in real time. Keep this tab open and visible until it finishes.', '');
        var mime = pickMime(), stream = null, rec = null, chunks = [];
        V.video.pause();
        seekTo(0).then(function () {
          stream = el.canvas.captureStream(60);
          try {
            if (!V.src) {
              V.ac = V.ac || new (window.AudioContext || window.webkitAudioContext)();
              V.src = V.ac.createMediaElementSource(V.video);
              V.dest = V.ac.createMediaStreamDestination();
              V.src.connect(V.dest);
            } else { try { V.src.disconnect(V.ac.destination); } catch (e) { /* ignore */ } }
            V.ac.resume();
            V.dest.stream.getAudioTracks().forEach(function (t) { stream.addTrack(t); });
          } catch (e) { /* no audio is fine */ }
          var bps = clamp(Math.round(V.W * V.H * 30 * 0.1), 2500000, 16000000), opts = { videoBitsPerSecond: bps };
          if (mime) opts.mimeType = mime;
          rec = new MediaRecorder(stream, opts);
          rec.ondataavailable = function (e) { if (e.data && e.data.size) chunks.push(e.data); };
          var stopped = new Promise(function (res) { rec.onstop = res; });
          var ended = new Promise(function (res) {
            var done = function () { V.video.removeEventListener('ended', done); V.endHook = null; res(); };
            V.video.addEventListener('ended', done); V.endHook = done;
          });
          rec.start(500);
          return V.video.play().then(function () { return ended; }).then(function () {
            return new Promise(function (r) { setTimeout(r, 300); });
          }).then(function () { rec.stop(); return stopped; });
        }).then(function () {
          if (V.cancel) { setStatus(el.status, 'Cancelled. Nothing was saved.', ''); return; }
          var type = ((rec && rec.mimeType) || mime || 'video/webm').split(';')[0];
          var blob = new Blob(chunks, { type: type }), ext = /mp4/.test(type) ? 'mp4' : 'webm';
          if (V.resultUrl) URL.revokeObjectURL(V.resultUrl);
          V.resultUrl = URL.createObjectURL(blob);
          el.resultVideo.src = V.resultUrl; el.dl.href = V.resultUrl; el.dl.download = V.name + '-no-watermark.' + ext;
          el.result.hidden = false;
          setStatus(el.status, 'Done. Your cleaned video is ready below.', 'ok');
        }).catch(function () {
          setStatus(el.status, 'Something went wrong while recording. Press play once on the preview, then try again.', 'err');
        }).then(function () {
          if (stream) stream.getTracks().forEach(function (t) { t.stop(); });
          try { if (V.src && V.ac) V.src.connect(V.ac.destination); } catch (e) { /* ignore */ }
          V.video.pause(); lock(false); seekTo(0).then(draw);
        });
      }

      el.input.addEventListener('change', function () { if (el.input.files[0]) load(el.input.files[0]); el.input.value = ''; });
      el.play.addEventListener('click', function () {
        if (!V.video) return;
        if (V.video.paused) { var p = V.video.play(); if (p && p.catch) p.catch(function () {}); } else V.video.pause();
      });
      el.seek.addEventListener('input', function () { if (V.video && V.video.duration) V.video.currentTime = el.seek.value / 1000 * V.video.duration; });
      el.grow.addEventListener('input', function () { el.growVal.textContent = el.grow.value + ' px'; });
      el.grow.addEventListener('change', function () { V.grow = +el.grow.value; rebuild(); });
      Array.prototype.forEach.call(document.querySelectorAll('input[name="vidShape"]'), function (r) {
        r.addEventListener('change', function () {
          if (V.sel && shape() === 'sparkle') { var s = Math.max(V.sel.w, V.sel.h); V.sel = { x: V.sel.x, y: V.sel.y, w: Math.min(s, V.W - V.sel.x), h: Math.min(s, V.H - V.sel.y) }; selector.place(); }
          rebuild();
        });
      });
      holdButton(el.compare, function () { V.compare = true; if (!V.playing) draw(); }, function () { V.compare = false; if (!V.playing) draw(); });
      el.go.addEventListener('click', exportVideo);
      el.cancel.addEventListener('click', function () { V.cancel = true; if (V.video) V.video.pause(); if (V.endHook) V.endHook(); });
      el.reset.addEventListener('click', function () { teardown(); el.work.hidden = true; el.drop.hidden = false; setStatus($('vidDropStatus'), ''); });

      return { load: load, busy: function () { return V.busy; } };
    }

    /* ====================== tabs, drop, paste, install ====================== */
    var image = initImage(), video = initVideo();

    function showTab(name) {
      ['image', 'video'].forEach(function (n) {
        var t = $('tab-' + n), p = $('panel-' + n), on = n === name;
        t.setAttribute('aria-selected', on ? 'true' : 'false'); t.tabIndex = on ? 0 : -1; p.hidden = !on;
      });
    }
    ['image', 'video'].forEach(function (n, i, arr) {
      var t = $('tab-' + n);
      t.addEventListener('click', function () { showTab(n); });
      t.addEventListener('keydown', function (e) {
        if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') {
          var next = arr[(i + (e.key === 'ArrowRight' ? 1 : arr.length - 1)) % arr.length];
          showTab(next); $('tab-' + next).focus();
        }
      });
    });

    function routeFile(file) {
      if (!file || video.busy()) return;
      if (/^image\//.test(file.type)) { showTab('image'); image.load(file); }
      else if (/^video\//.test(file.type)) { showTab('video'); video.load(file); }
      else {
        var tgt = !$('panel-video').hidden ? $('vidDropStatus') : $('imgDropStatus');
        setStatus(tgt, 'That file type is not supported. Please choose an image or a video.', 'err');
      }
    }
    ['imgDrop', 'vidDrop'].forEach(function (id) {
      var z = $(id);
      ['dragenter', 'dragover'].forEach(function (n) { z.addEventListener(n, function () { z.classList.add('over'); }); });
      ['dragleave', 'drop'].forEach(function (n) { z.addEventListener(n, function () { z.classList.remove('over'); }); });
    });
    window.addEventListener('dragover', function (e) { e.preventDefault(); });
    window.addEventListener('drop', function (e) {
      e.preventDefault();
      if (e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files[0]) routeFile(e.dataTransfer.files[0]);
    });
    document.addEventListener('paste', function (e) {
      var f = e.clipboardData && e.clipboardData.files && e.clipboardData.files[0];
      if (f) { e.preventDefault(); routeFile(f); }
    });

    var deferred = null, ib = $('installBtn');
    window.addEventListener('beforeinstallprompt', function (e) { e.preventDefault(); deferred = e; ib.hidden = false; });
    ib.addEventListener('click', function () {
      if (!deferred) return;
      deferred.prompt();
      deferred.userChoice.then(function () { deferred = null; ib.hidden = true; });
    });
    window.addEventListener('appinstalled', function () { ib.hidden = true; });

    var yr = $('year'); if (yr) yr.textContent = new Date().getFullYear();
    if ('serviceWorker' in navigator && /^https?:$/.test(location.protocol)) {
      window.addEventListener('load', function () { navigator.serviceWorker.register('sw.js').catch(function () {}); });
    }
  }

  return { core: core, start: start };
});
