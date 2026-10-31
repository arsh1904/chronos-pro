/* =====================================================================
   Release check: the analysis and the repair steps behind its Fix buttons
   (added onto AudioStore so main.js and features.js stay untouched)
   ===================================================================== */

// ---- one scan that measures everything a release needs ----
AudioStore.prototype.analyzeRelease = async function (buf) {
    const sr = buf.sampleRate, n = buf.length, ch = buf.numberOfChannels;
    const chs = []; for (let c = 0; c < ch; c++) chs.push(buf.getChannelData(c));
    const R = { sr, ch, duration: buf.duration, length: n };

    // ---- pass 1: peaks, clipping, DC offset, stereo statistics, 100 ms energy windows ----
    const win = Math.max(1, Math.floor(sr * 0.1)), nw = Math.floor(n / win), rmsW = new Float32Array(nw);
    const sums = new Float64Array(ch), runs = new Int32Array(ch), clipTimes = [];
    let peak = 0, clipSamples = 0, clipEvents = 0, sLL = 0, sRR = 0, sLR = 0, mid2 = 0, wEnergy = 0, wi = 0;
    for (let i = 0; i < n; i++) {
        let e = 0;
        for (let c = 0; c < ch; c++) {
            const v = chs[c][i], a = v < 0 ? -v : v;
            if (a > peak) peak = a;
            sums[c] += v; e += v * v;
            if (a >= 0.999) {
                runs[c]++; clipSamples++;
                if (runs[c] === 3) { clipEvents++; if (clipTimes.length < 200) clipTimes.push(i / sr); }
            } else runs[c] = 0;
        }
        if (ch >= 2) { const L = chs[0][i], Rr = chs[1][i]; sLL += L * L; sRR += Rr * Rr; sLR += L * Rr; const m = (L + Rr) / 2; mid2 += m * m; }
        wEnergy += e / ch;
        if ((i + 1) % win === 0 && wi < nw) { rmsW[wi++] = Math.sqrt(wEnergy / win); wEnergy = 0; }
        if ((i & 0x7ffff) === 0) await yieldUI();
    }
    R.peakDb = peak > 0 ? 20 * Math.log10(peak) : -Infinity;
    R.clipEvents = clipEvents; R.clipSamples = clipSamples; R.clipTimes = clipTimes;
    R.dc = Math.max(...Array.from(sums, (s) => Math.abs(s / Math.max(1, n))));

    // ---- stereo: how well the two sides agree, and what survives a mono phone speaker ----
    if (ch >= 2 && sLL > 0 && sRR > 0) {
        R.correlation = sLR / Math.sqrt(sLL * sRR);
        R.monoLossDb = mid2 > 0 ? 10 * Math.log10(mid2 / ((sLL + sRR) / 2)) : -60;
    } else { R.correlation = null; R.monoLossDb = 0; }

    // ---- true peak: peaks that only exist between samples (4x oversampling with a windowed sinc, like the loudness standard) ----
    const TAPS = 8, H = [];
    for (let k = 1; k < 4; k++) {
        const t = k / 4, row = new Float32Array(2 * TAPS);
        for (let m = -TAPS + 1; m <= TAPS; m++) {
            const u = m - t, sinc = Math.abs(u) < 1e-9 ? 1 : Math.sin(Math.PI * u) / (Math.PI * u), w = 0.5 + 0.5 * Math.cos(Math.PI * u / TAPS);
            row[m + TAPS - 1] = sinc * w;
        }
        H.push(row);
    }
    let tp = peak;
    for (let c = 0; c < ch; c++) {
        const x = chs[c];
        for (let i = TAPS; i < n - TAPS; i++) {
            const a1 = x[i] < 0 ? -x[i] : x[i], a2 = x[i + 1] < 0 ? -x[i + 1] : x[i + 1];
            if (a1 < 0.45 && a2 < 0.45) continue;
            for (let k = 0; k < 3; k++) {
                const row = H[k]; let v = 0;
                for (let m = 0; m < 2 * TAPS; m++) v += x[i - TAPS + 1 + m] * row[m];
                const av = v < 0 ? -v : v; if (av > tp) tp = av;
            }
            if ((i & 0x7ffff) === 0) await yieldUI();
        }
    }
    R.truePeakDb = tp > 0 ? 20 * Math.log10(tp) : -Infinity;

    // ---- noise floor: how loud are the quietest moments? ----
    const live = Array.from(rmsW).filter((v) => v > 1e-6).sort((a, b) => a - b);
    R.noiseFloorDb = live.length ? 20 * Math.log10(live[Math.floor(live.length * 0.05)]) : -Infinity;
    R.digitalSilenceShare = nw ? 1 - live.length / nw : 0;
    R.medianDb = live.length ? 20 * Math.log10(live[Math.floor(live.length * 0.5)]) : -Infinity;
    R.hasQuietMoments = live.length > 4 && (R.medianDb - R.noiseFloorDb) >= 15;

    // ---- silence at the start and end, and abrupt edges ----
    const quiet = Math.pow(10, -60 / 20);
    let lead = 0; while (lead < nw && rmsW[lead] < quiet) lead++;
    let trail = 0; while (trail < nw && rmsW[nw - 1 - trail] < quiet) trail++;
    R.leadSilence = lead >= nw ? R.duration : lead * 0.1; R.trailSilence = trail >= nw ? 0 : trail * 0.1;
    const edge = Math.max(1, Math.floor(sr * 0.003)); let eS = 0, eE = 0;
    for (let c = 0; c < ch; c++) for (let i = 0; i < Math.min(edge, n); i++) { eS = Math.max(eS, Math.abs(chs[c][i])); eE = Math.max(eE, Math.abs(chs[c][n - 1 - i])); }
    R.startLevel = eS; R.endLevel = eE;

    // ---- mains hum: a steady tone at 50/60 Hz that stands out from its neighbours ----
    const N = Math.min(n, Math.floor(sr * 60)), mono = new Float32Array(N);
    for (let c = 0; c < ch; c++) { const x = chs[c]; for (let i = 0; i < N; i++) mono[i] += x[i] / ch; }
    const tone = (f) => {
        let re = 0, im = 0, ws = 0; const w = 2 * Math.PI * f / sr, cr = Math.cos(w), ci = Math.sin(w); let pr = 1, pi = 0;
        for (let i = 0; i < N; i++) {
            const hann = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / (N - 1)), v = mono[i] * hann;
            re += v * pr; im -= v * pi; ws += hann;
            const nr = pr * cr - pi * ci; pi = pr * ci + pi * cr; pr = nr;
        }
        return 2 * Math.hypot(re, im) / ws;
    };
    R.hum = { hz: null, level: 0, prominenceDb: 0 };
    if (N > sr * 2) {
        for (const f of [50, 60]) {
            const a = tone(f), nb = (tone(f - 5) + tone(f + 5) + tone(f - 8) + tone(f + 8)) / 4, h2 = tone(f * 2), h2n = (tone(f * 2 - 6) + tone(f * 2 + 6)) / 2;
            const prom = 20 * Math.log10((a + 1e-9) / (nb + 1e-9)), prom2 = 20 * Math.log10((h2 + 1e-9) / (h2n + 1e-9));
            if (a > R.hum.level && prom > 12 && prom2 > 6) R.hum = { hz: f, level: a, prominenceDb: prom };
        }
        await yieldUI();
    }

    // ---- clicks: single-sample spikes far above the normal wobble ----
    const clickTimes = []; let clicks = 0;
    {
        const x = chs[0]; let avg = 0.002;
        for (let i = 1; i < n - 1; i++) {
            const e = Math.abs(x[i] - (x[i - 1] + x[i + 1]) / 2);
            if (e > 8 * avg + 0.03) {
                const eNext = i < n - 2 ? Math.abs(x[i + 1] - (x[i] + x[i + 2]) / 2) : 0, ePrev = i > 1 ? Math.abs(x[i - 1] - (x[i - 2] + x[i]) / 2) : 0;
                if (e >= eNext && e >= ePrev) { clicks++; if (clickTimes.length < 100) clickTimes.push(i / sr); }
            } else avg += (e - avg) * 0.0008;
            if ((i & 0x7ffff) === 0) await yieldUI();
        }
    }
    R.clicks = clicks; R.clickTimes = clickTimes;

    // ---- loudness ----
    await yieldUI();
    const m = this.measureLoudness(buf);
    R.lufs = m.lufs; R.lra = m.lra;
    return R;
};

// ---- repair steps ----
AudioStore.prototype.fxDC = function (buf) {
    for (let c = 0; c < buf.numberOfChannels; c++) {
        const d = buf.getChannelData(c); let m = 0;
        for (let i = 0; i < d.length; i++) m += d[i];
        m /= Math.max(1, d.length);
        for (let i = 0; i < d.length; i++) d[i] -= m;
    }
    return buf;
};

// Rebuild flat-topped (clipped) peaks with a smooth curve through the surrounding samples
AudioStore.prototype.fxDeclip = function (buf) {
    let fixed = 0;
    for (let c = 0; c < buf.numberOfChannels; c++) {
        const x = buf.getChannelData(c), n = x.length;
        let i = 2;
        while (i < n - 2) {
            if (Math.abs(x[i]) >= 0.999) {
                let j = i; while (j < n - 2 && Math.abs(x[j + 1]) >= 0.999 && Math.sign(x[j + 1]) === Math.sign(x[i])) j++;
                if (j - i + 1 >= 3) {
                    const a = i - 1, b = j + 1, len = b - a, m0 = (x[a] - x[a - 1]) * len, m1 = (x[b + 1] - x[b]) * len, y0 = x[a], y1 = x[b];
                    for (let k = 1; k < len; k++) {
                        const t = k / len, t2 = t * t, t3 = t2 * t;
                        x[a + k] = (2 * t3 - 3 * t2 + 1) * y0 + (t3 - 2 * t2 + t) * m0 + (-2 * t3 + 3 * t2) * y1 + (t3 - t2) * m1;
                    }
                    fixed++;
                }
                i = j + 1;
            } else i++;
        }
    }
    this.lastDeclip = fixed;
    return buf;
};

// Remove long silence at the very start and end (keeping a natural breath of it)
AudioStore.prototype.trimSilenceEnds = function (buf, { keepLead = 0.25, keepTrail = 0.6, thresholdDb = -60 } = {}) {
    const sr = buf.sampleRate, n = buf.length, thr = Math.pow(10, thresholdDb / 20), win = Math.floor(sr * 0.05);
    const loud = (i) => { let m = 0; for (let c = 0; c < buf.numberOfChannels; c++) { const d = buf.getChannelData(c); for (let k = i; k < Math.min(n, i + win); k++) { const a = Math.abs(d[k]); if (a > m) m = a; } } return m > thr; };
    let a = 0; while (a < n && !loud(a)) a += win;
    let b = n; while (b > a && !loud(Math.max(0, b - win))) b -= win;
    const s = Math.max(0, a - Math.floor(keepLead * sr)), e = Math.min(n, b + Math.floor(keepTrail * sr));
    if (e - s <= sr * 0.2 || (s === 0 && e === n)) return { buf, lead: 0 };
    const out = this.ctx.createBuffer(buf.numberOfChannels, e - s, sr);
    for (let c = 0; c < buf.numberOfChannels; c++) out.getChannelData(c).set(buf.getChannelData(c).subarray(s, e));
    return { buf: out, lead: s / sr };
};

// Highest peak including peaks that only exist between samples (4x oversampled, windowed sinc). Linear value.
AudioStore.prototype.truePeakLinear = function (buf) {
    const ch = buf.numberOfChannels, n = buf.length, TAPS = 8, H = [];
    for (let k = 1; k < 4; k++) {
        const t = k / 4, row = new Float32Array(2 * TAPS);
        for (let m = -TAPS + 1; m <= TAPS; m++) {
            const u = m - t, sinc = Math.abs(u) < 1e-9 ? 1 : Math.sin(Math.PI * u) / (Math.PI * u), w = 0.5 + 0.5 * Math.cos(Math.PI * u / TAPS);
            row[m + TAPS - 1] = sinc * w;
        }
        H.push(row);
    }
    let tp = 0;
    for (let c = 0; c < ch; c++) {
        const x = buf.getChannelData(c);
        for (let i = 0; i < n; i++) { const a = x[i] < 0 ? -x[i] : x[i]; if (a > tp) tp = a; }
        for (let i = TAPS; i < n - TAPS; i++) {
            const a1 = x[i] < 0 ? -x[i] : x[i], a2 = x[i + 1] < 0 ? -x[i + 1] : x[i + 1];
            if (a1 < 0.45 && a2 < 0.45) continue;
            for (let k = 0; k < 3; k++) {
                const row = H[k]; let v = 0;
                for (let m = 0; m < 2 * TAPS; m++) v += x[i - TAPS + 1 + m] * row[m];
                const av = v < 0 ? -v : v; if (av > tp) tp = av;
            }
        }
    }
    return tp;
};

// Limit so the TRUE peak (not just the sample peak) stays under the ceiling.
// fxLimit works on sample peaks, which can leave inter-sample peaks above the ceiling,
// so after limiting we measure the true peak and trim by exactly the overshoot.
AudioStore.prototype.limitTruePeak = async function (buf, ceilingDb = -1) {
    await this.fxLimit(buf, ceilingDb);
    const ceil = Math.pow(10, ceilingDb / 20) * 0.9995; // tiny margin so rounding never lands on the line
    for (let pass = 0; pass < 3; pass++) {
        await yieldUI();
        const tp = this.truePeakLinear(buf);
        if (tp <= ceil) break;
        this._gain(buf, ceil / tp);
    }
    return buf;
};

// Bring a track to a loudness target without exceeding the peak ceiling
AudioStore.prototype.levelTo = async function (buf, target, ceiling = -1) {
    this.matchLoudness(buf, target);
    await this.limitTruePeak(buf, ceiling);
    for (let i = 0; i < 2; i++) {
        const m = this.measureLoudness(buf);
        if (!isFinite(m.lufs) || Math.abs(m.lufs - target) < 0.4) break;
        this._gain(buf, Math.pow(10, (target - m.lufs) / 20));
        await this.limitTruePeak(buf, ceiling);
    }
    return buf;
};

// Sound phrases between silences (used to fit lyrics to the singing)
AudioStore.prototype.findPhrases = function (buf, thresholdDb = -45, minSilenceMs = 250) {
    const sil = this.detectSilences(buf, thresholdDb, minSilenceMs), out = []; let cur = 0;
    for (const [s, e] of sil) { if (s - cur > 0.15) out.push([cur, s]); cur = e; }
    if (buf.duration - cur > 0.15) out.push([cur, buf.duration]);
    return out;
};

// Find the beat grid: tempo, where the first beat falls, and refine over the whole song so it does not drift
AudioStore.prototype.detectBeats = async function (buf) {
    const sr = buf.sampleRate, ch = buf.numberOfChannels, maxN = Math.min(buf.length, Math.floor(sr * 600));
    const hop = Math.max(1, Math.floor(sr * 0.005)), F = Math.floor(maxN / hop);
    if (F < 400) return null;
    const env = new Float32Array(F);
    for (let f = 0; f < F; f++) {
        let sum = 0; const s = f * hop;
        for (let c = 0; c < ch; c++) { const d = buf.getChannelData(c); for (let i = 0; i < hop; i++) { const v = d[s + i]; sum += v * v; } }
        env[f] = Math.log(1 + 1000 * Math.sqrt(sum / (hop * ch)));
        if ((f & 0x3fff) === 0) await yieldUI();
    }
    const flux = new Float32Array(F); let mean = 0;
    for (let f = 1; f < F; f++) { flux[f] = Math.max(0, env[f] - env[f - 1]); mean += flux[f]; }
    mean /= F; for (let f = 0; f < F; f++) flux[f] = Math.max(0, flux[f] - mean);
    const fps = sr / hop, minLag = Math.floor(fps * 60 / 200), maxLag = Math.ceil(fps * 60 / 60);
    const lim = Math.min(F, Math.floor(fps * 90)), ac = new Float64Array(maxLag + 2);
    for (let lag = minLag; lag <= maxLag; lag++) { let s = 0; for (let f = 0; f + lag < lim; f++) s += flux[f] * flux[f + lag]; ac[lag] = s / (lim - lag); }
    let best = minLag, bs = -1;
    for (let lag = minLag; lag <= maxLag; lag++) { const bpm = 60 * fps / lag, sc = ac[lag] * Math.exp(-Math.pow(Math.log2(bpm / 110), 2) / 1.6); if (sc > bs) { bs = sc; best = lag; } }
    let ac0 = 0; for (let f = 0; f < lim; f++) ac0 += flux[f] * flux[f]; ac0 /= lim;
    if (!(ac0 > 1e-6) || ac[best] / ac0 < 0.3) return null;
    // refine the period and find the phase by scoring a comb of beats over the whole track
    const at = (x) => { const i = Math.floor(x); if (i < 0 || i >= F - 1) return 0; const fr = x - i; return flux[i] * (1 - fr) + flux[i + 1] * fr; };
    let bestScore = -1, bestP = best, bestO = 0;
    for (let k = -50; k <= 50; k++) {
        const p = best * (1 + k * 0.0002);
        for (let o = 0; o < p; o += 0.5) { let sc = 0; for (let x = o; x < F - 1; x += p) sc += at(x); if (sc > bestScore) { bestScore = sc; bestP = p; bestO = o; } }
        if ((k & 7) === 0) await yieldUI();
    }
    const period = bestP * hop / sr;
    return { bpm: 60 / period, period, offset: bestO * hop / sr, strength: ac[best] / ac0 };
};