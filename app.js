/* Chronos Pro - bundled app (audio engine + editor + studio features) */
// ---------- shared DSP helpers ----------
function makeFFT(n) {
    const cos = new Float64Array(n / 2), sin = new Float64Array(n / 2), rev = new Uint32Array(n), bits = Math.round(Math.log2(n));
    for (let k = 0; k < n / 2; k++) { cos[k] = Math.cos(2 * Math.PI * k / n); sin[k] = Math.sin(2 * Math.PI * k / n); }
    for (let i = 0; i < n; i++) { let r = 0, x = i; for (let b = 0; b < bits; b++) { r = (r << 1) | (x & 1); x >>= 1; } rev[i] = r; }
    function forward(re, im) {
        for (let i = 0; i < n; i++) { const j = rev[i]; if (j > i) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
        for (let size = 2; size <= n; size <<= 1) {
            const half = size >> 1, step = n / size;
            for (let i = 0; i < n; i += size) {
                for (let j = 0, k = 0; j < half; j++, k += step) {
                    const a = i + j, b = a + half;
                    const tr = re[b] * cos[k] + im[b] * sin[k], ti = im[b] * cos[k] - re[b] * sin[k];
                    re[b] = re[a] - tr; im[b] = im[a] - ti; re[a] += tr; im[a] += ti;
                }
            }
        }
    }
    function inverse(re, im) {
        for (let i = 0; i < n; i++) im[i] = -im[i];
        forward(re, im);
        for (let i = 0; i < n; i++) { re[i] /= n; im[i] = -im[i] / n; }
    }
    return { n, forward, inverse };
}
const hannWin = (n) => { const w = new Float32Array(n); for (let i = 0; i < n; i++) w[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / n); return w; };
let _lastYield = 0;
// Long jobs call this so the page stays responsive (spinners keep spinning)
async function yieldUI() {
    const now = performance.now();
    if (now - _lastYield > 40) { await new Promise(r => setTimeout(r, 0)); _lastYield = performance.now(); }
}

class AudioStore {
    constructor() {
        this.ctx = new (window.AudioContext || window.webkitAudioContext)();
        this.audioBuffer = null;
        this.originalBuffer = null;
        this.sourceNode = null;

        this.masterGain = this.ctx.createGain();
        this.trackGain = this.ctx.createGain();
        this.volumeGain = this.ctx.createGain();
        this.filterNode = this.ctx.createBiquadFilter();
        this.filterNode.type = 'lowpass';
        this.filterNode.frequency.value = 20000;

        // Live 3-band EQ
        const mk = (type, freq, q) => {
            const n = this.ctx.createBiquadFilter();
            n.type = type; n.frequency.value = freq; n.Q.value = q; n.gain.value = 0;
            return n;
        };
        this.eq = { low: mk('lowshelf', 120, 0.7), mid: mk('peaking', 1000, 1), high: mk('highshelf', 8000, 0.7) };

        // Chain: source -> trackGain -> studio filter -> EQ -> volume -> master -> speakers
        this.abGain = this.ctx.createGain();
        this.abGain.connect(this.trackGain);
        this.trackGain.connect(this.filterNode);
        this.filterNode.connect(this.eq.low);
        this.eq.low.connect(this.eq.mid);
        this.eq.mid.connect(this.eq.high);
        this.comp = this.ctx.createDynamicsCompressor();
        this.compMakeup = this.ctx.createGain();
        this.panner = this.ctx.createStereoPanner();
        this.eq.high.connect(this.comp);
        this.comp.connect(this.compMakeup);
        this.compMakeup.connect(this.panner);
        this.panner.connect(this.volumeGain);
        this.volumeGain.connect(this.masterGain);
        this.masterGain.connect(this.ctx.destination);

        // Analysis taps (read only)
        this.splitter = this.ctx.createChannelSplitter(2);
        this.analyserL = this.ctx.createAnalyser();
        this.analyserR = this.ctx.createAnalyser();
        this.analyserVox = this.ctx.createAnalyser();
        this.analyserSpec = this.ctx.createAnalyser();
        [this.analyserL, this.analyserR, this.analyserVox].forEach(a => { a.fftSize = 1024; });
        this.analyserSpec.fftSize = 2048;
        this.analyserSpec.smoothingTimeConstant = 0.72;
        this.analyserSpec.minDecibels = -90;
        this.analyserSpec.maxDecibels = -10;
        this.masterGain.connect(this.splitter);
        this.splitter.connect(this.analyserL, 0);
        this.splitter.connect(this.analyserR, 1);
        this.masterGain.connect(this.analyserSpec);
        this.trackGain.connect(this.analyserVox);
        this._meterBuf = new Float32Array(1024);
        this._specBuf = new Uint8Array(this.analyserSpec.frequencyBinCount);
        this._waveBuf = new Uint8Array(this.analyserSpec.fftSize);

        this.isPlaying = false;
        this.isLooping = false;
        this.isEffectActive = false;
        this.startTime = 0;
        this.rate = 1; // playback speed
        this.pauseOffset = 0;
        this.history = [];
        this.redoStack = [];
        this.maxHistory = 6;
        this.region = null;          // { a, b } while playing/looping a selection
        this.clipboard = null;
        this.noiseProfile = null;
        this.compCfg = { enabled: false, threshold: -24, ratio: 3, attack: 10, release: 200, knee: 12, makeup: 0 };
        this.applyComp();
        this.onEnded = null;
        this._rms = null;
    }

    // ---------- helpers ----------
    cloneBuffer(buffer) {
        const clone = this.ctx.createBuffer(buffer.numberOfChannels, buffer.length, buffer.sampleRate);
        for (let c = 0; c < buffer.numberOfChannels; c++) clone.copyToChannel(buffer.getChannelData(c), c);
        return clone;
    }

    _peak(analyser) {
        analyser.getFloatTimeDomainData(this._meterBuf);
        let p = 0;
        for (let i = 0; i < this._meterBuf.length; i++) { const v = Math.abs(this._meterBuf[i]); if (v > p) p = v; }
        return p;
    }
    getLevels() { return { l: this._peak(this.analyserL), r: this._peak(this.analyserR), vox: this._peak(this.analyserVox) }; }
    getSpectrum() { this.analyserSpec.getByteFrequencyData(this._specBuf); return this._specBuf; }
    getWave() { this.analyserSpec.getByteTimeDomainData(this._waveBuf); return this._waveBuf; }

    getInfo() {
        if (!this.audioBuffer) return null;
        return { duration: this.audioBuffer.duration, sampleRate: this.audioBuffer.sampleRate, channels: this.audioBuffer.numberOfChannels };
    }

    // ---------- history (undo / redo / time travel) ----------
    snapshot(label = 'Edit', meta = null) {
        if (!this.audioBuffer) return;
        this.history.push({ label, buffer: this.cloneBuffer(this.audioBuffer), meta });
        if (this.history.length > this.maxHistory) this.history.shift();
        this.redoStack = [];
    }
    canUndo() { return this.history.length > 0; }
    canRedo() { return this.redoStack.length > 0; }
    undo(meta = null) { // meta = the current state's extras (markers), kept so redo can bring them back
        if (!this.history.length) return null;
        this.stop();
        const entry = this.history.pop();
        this.redoStack.push({ label: entry.label, buffer: this.audioBuffer, meta });
        this.audioBuffer = entry.buffer;
        this.restoredMeta = entry.meta;
        return this.audioBuffer;
    }
    redo(meta = null) {
        if (!this.redoStack.length) return null;
        this.stop();
        const entry = this.redoStack.pop();
        this.history.push({ label: entry.label, buffer: this.audioBuffer, meta });
        this.audioBuffer = entry.buffer;
        this.restoredMeta = entry.meta;
        return this.audioBuffer;
    }
    getTimeline() {
        return { past: this.history.map(h => h.label), future: this.redoStack.map(h => h.label).reverse() };
    }

    // ---------- loading ----------
    async loadAudio(arrayBuffer) {
        if (this.ctx.state === 'suspended') await Promise.race([this.ctx.resume(), new Promise((r) => setTimeout(r, 600))]);
        this.audioBuffer = await this.ctx.decodeAudioData(arrayBuffer);
        this.originalBuffer = this.cloneBuffer(this.audioBuffer);
        this.history = []; this.redoStack = [];
        this.stopSource();
        this.pauseOffset = 0;
        this.isPlaying = false;
        return this.audioBuffer;
    }
    resetToOriginal() {
        if (!this.originalBuffer) return false;
        this.stop();
        this.audioBuffer = this.cloneBuffer(this.originalBuffer);
        this.history = []; this.redoStack = [];
        this.pauseOffset = 0;
        return this.audioBuffer;
    }

    // ---------- transport ----------
    play() {
        if (!this.audioBuffer) return;
        if (this.ctx.state === 'suspended') this.ctx.resume();
        this.stopSource();
        const src = this.ctx.createBufferSource(), r = this.region;
        src.buffer = this.audioBuffer;
        src.loop = this.isLooping;
        src.playbackRate.value = this.rate;
        src.connect(this.abGain);
        let offset = this.pauseOffset;
        if (r) {
            if (offset < r.a || offset >= r.b) offset = r.a;
            if (this.isLooping) { src.loopStart = r.a; src.loopEnd = r.b; }
        } else if (offset >= this.getDuration()) offset = 0;
        src.onended = () => {
            if (this.sourceNode === src && !this.isLooping) {
                this.sourceNode = null;
                this.isPlaying = false;
                if (r) this.pauseOffset = r.a;
                if (this.onEnded) this.onEnded(!!r);
            }
        };
        this.sourceNode = src;
        if (r && !this.isLooping) src.start(0, offset, Math.max(0.001, r.b - offset)); else src.start(0, offset);
        this.startTime = this.ctx.currentTime - offset / this.rate;
        this.isPlaying = true;
    }
    pause() {
        if (!this.isPlaying) return;
        this.pauseOffset = this.getCurrentTime();
        this.stopSource();
        this.isPlaying = false;
    }
    stop() { this.stopSource(); this.pauseOffset = 0; this.isPlaying = false; }
    stopSource() {
        if (this.sourceNode) {
            const src = this.sourceNode;
            this.sourceNode = null;
            src.onended = null;
            try { src.stop(); } catch (e) { }
            src.disconnect();
        }
    }
    seek(seconds) {
        const wasPlaying = this.isPlaying;
        if (wasPlaying) this.pause();
        this.pauseOffset = Math.max(0, Math.min(seconds, this.getDuration()));
        if (wasPlaying) this.play();
    }
    getCurrentTime() {
        if (!this.isPlaying) return this.pauseOffset;
        const raw = (this.ctx.currentTime - this.startTime) * this.rate, d = this.getDuration(), r = this.region;
        if (r) {
            if (this.isLooping) return raw < r.b ? Math.max(raw, r.a) : r.a + ((raw - r.a) % (r.b - r.a));
            return Math.min(raw, r.b);
        }
        if (this.isLooping) return d > 0 ? raw % d : 0;
        return Math.min(raw, d);
    }
    getDuration() { return this.audioBuffer ? this.audioBuffer.duration : 0; }
    setVolume(v) { this.volumeGain.gain.value = v; }
    setMasterVolume(v) { this.masterGain.gain.value = v; }
    setVoiceVolume(v) { this.trackGain.gain.value = v; }
    toggleLoop() {
        this.isLooping = !this.isLooping;
        if (this.isPlaying && this.region) { // a region source can't change its looping mid-flight, so restart from here
            this.pauseOffset = this.getCurrentTime();
            this.stopSource(); this.isPlaying = false; this.play();
        } else if (this.sourceNode) this.sourceNode.loop = this.isLooping;
        return this.isLooping;
    }
    toggleEffect() {
        this.isEffectActive = !this.isEffectActive;
        this.filterNode.frequency.value = this.isEffectActive ? 1200 : 20000;
        return this.isEffectActive;
    }

    // ---------- live EQ ----------
    getEQ() {
        const o = {};
        for (const k of ['low', 'mid', 'high']) o[k] = { freq: this.eq[k].frequency.value, gain: this.eq[k].gain.value, q: this.eq[k].Q.value };
        return o;
    }
    setEQ(band, p) {
        const n = this.eq[band];
        if (p.freq !== undefined) n.frequency.value = p.freq;
        if (p.gain !== undefined) n.gain.value = p.gain;
        if (p.q !== undefined) n.Q.value = p.q;
    }
    resetEQ() {
        const d = { low: 120, mid: 1000, high: 8000 };
        for (const k of ['low', 'mid', 'high']) this.setEQ(k, { freq: d[k], gain: 0, q: k === 'mid' ? 1 : 0.7 });
    }
    eqIsFlat() { return ['low', 'mid', 'high'].every(k => Math.abs(this.eq[k].gain.value) < 0.05); }
    eqResponse(freqs) {
        const out = new Float32Array(freqs.length);
        const mag = new Float32Array(freqs.length), ph = new Float32Array(freqs.length);
        for (const k of ['low', 'mid', 'high']) {
            this.eq[k].getFrequencyResponse(freqs, mag, ph);
            for (let i = 0; i < freqs.length; i++) out[i] += 20 * Math.log10(Math.max(mag[i], 1e-6));
        }
        return out;
    }

    // ---------- region plumbing ----------
    _clampSample(sec) { return Math.max(0, Math.min(this.audioBuffer.length, Math.floor(sec * this.audioBuffer.sampleRate))); }

    extract(startSec, endSec) {
        const b = this.audioBuffer, s = this._clampSample(startSec), e = this._clampSample(endSec);
        const out = this.ctx.createBuffer(b.numberOfChannels, Math.max(1, e - s), b.sampleRate);
        for (let c = 0; c < b.numberOfChannels; c++) out.getChannelData(c).set(b.getChannelData(c).subarray(s, e));
        return out;
    }

    splice(startSec, endSec, proc) {
        const b = this.audioBuffer, s = this._clampSample(startSec), e = this._clampSample(endSec);
        const ch = b.numberOfChannels;
        const out = this.ctx.createBuffer(ch, s + proc.length + (b.length - e), b.sampleRate);
        for (let c = 0; c < ch; c++) {
            const d = out.getChannelData(c);
            d.set(b.getChannelData(c).subarray(0, s), 0);
            d.set(proc.getChannelData(Math.min(c, proc.numberOfChannels - 1)), s);
            d.set(b.getChannelData(c).subarray(e), s + proc.length);
        }
        return out;
    }

    _fit(buf, length) {
        const out = this.ctx.createBuffer(buf.numberOfChannels, length, buf.sampleRate);
        for (let c = 0; c < buf.numberOfChannels; c++) out.getChannelData(c).set(buf.getChannelData(c).subarray(0, length));
        return out;
    }

    // Run fn on a region (or the whole track when startSec is null) and splice the result back.
    async processRegion(startSec, endSec, fn, { keepLength = false } = {}) {
        if (!this.audioBuffer) return;
        const whole = startSec == null;
        const s = whole ? 0 : startSec, e = whole ? this.getDuration() : endSec;
        const before = this.audioBuffer.length;
        const sub = this.extract(s, e);
        let out = await fn(sub);
        if (!whole && keepLength && out.length !== sub.length) out = this._fit(out, sub.length);
        this.audioBuffer = this.splice(s, e, out);
        if (this.audioBuffer.length !== before) this.pauseOffset = 0;
    }

    // ---------- pure DSP (take a buffer, return a buffer) ----------
    fxFadeIn(buf, sec = 3) {
        const n = Math.min(Math.floor(buf.sampleRate * sec), buf.length);
        for (let c = 0; c < buf.numberOfChannels; c++) { const d = buf.getChannelData(c); for (let i = 0; i < n; i++) d[i] *= i / n; }
        return buf;
    }
    fxFadeOut(buf, sec = 3) {
        const n = Math.min(Math.floor(buf.sampleRate * sec), buf.length), st = buf.length - n;
        for (let c = 0; c < buf.numberOfChannels; c++) { const d = buf.getChannelData(c); for (let i = 0; i < n; i++) d[st + i] *= 1 - i / n; }
        return buf;
    }
    fxNormalize(buf) {
        let peak = 0;
        for (let c = 0; c < buf.numberOfChannels; c++) { const d = buf.getChannelData(c); for (let i = 0; i < d.length; i++) { const a = Math.abs(d[i]); if (a > peak) peak = a; } }
        if (peak > 0) this._gain(buf, 1 / peak);
        return buf;
    }
    fxReverse(buf) {
        for (let c = 0; c < buf.numberOfChannels; c++) Array.prototype.reverse.call(buf.getChannelData(c));
        return buf;
    }
    fxRobo(buf) {
        const delay = Math.floor(buf.sampleRate / 130.81); // C3
        for (let c = 0; c < buf.numberOfChannels; c++) {
            const d = buf.getChannelData(c);
            for (let i = d.length - 1; i >= delay; i--) d[i] = d[i] * 0.5 + d[i - delay] * 0.5;
        }
        return this.fxNormalize(buf);
    }
    fxResample(buf, factor) { // factor > 1 = faster and higher
        const newLen = Math.max(1, Math.floor(buf.length / factor));
        const out = this.ctx.createBuffer(buf.numberOfChannels, newLen, buf.sampleRate);
        for (let c = 0; c < buf.numberOfChannels; c++) {
            const src = buf.getChannelData(c), dst = out.getChannelData(c);
            for (let i = 0; i < newLen; i++) {
                const p = i * factor, i0 = Math.floor(p), f = p - i0;
                dst[i] = src[i0] * (1 - f) + (src[Math.min(i0 + 1, src.length - 1)] * f);
            }
        }
        return out;
    }
    _gain(buf, g) {
        for (let c = 0; c < buf.numberOfChannels; c++) {
            const d = buf.getChannelData(c);
            for (let i = 0; i < d.length; i++) {
                let x = d[i] * g;
                const a = Math.abs(x);
                if (a > 0.9) x = Math.sign(x) * (0.9 + 0.1 * Math.tanh((a - 0.9) / 0.1)); // soft limiter
                d[i] = x;
            }
        }
        return buf;
    }

    // ---------- offline rendering (filters, reverb, etc.) ----------
    async renderOffline(buf, build, tailSec = 0) {
        const sr = buf.sampleRate, len = buf.length + Math.floor(tailSec * sr);
        const off = new OfflineAudioContext(buf.numberOfChannels, len, sr);
        const src = off.createBufferSource();
        src.buffer = buf;
        build(off, src).connect(off.destination);
        src.start();
        return off.startRendering();
    }

    _biquad(off, type, freq, q = 0.7, gain = 0) {
        const n = off.createBiquadFilter();
        n.type = type; n.frequency.value = freq; n.Q.value = q; n.gain.value = gain;
        return n;
    }
    _chain(src, nodes) { let prev = src; for (const n of nodes) { prev.connect(n); prev = n; } return prev; }

    _makeIR(sec, decay) {
        const sr = this.ctx.sampleRate, len = Math.floor(sr * sec);
        const ir = this.ctx.createBuffer(2, len, sr);
        for (let c = 0; c < 2; c++) {
            const d = ir.getChannelData(c);
            let lp = 0;
            for (let i = 0; i < len; i++) {
                const t = i / len;
                lp += ((Math.random() * 2 - 1) - lp) * (0.85 - 0.7 * t); // tail gets darker
                d[i] = lp * Math.pow(1 - t, decay);
            }
        }
        return ir;
    }

    reverb(buf, { sec, decay, wet, tail }) {
        const ir = this._makeIR(sec, decay);
        return this.renderOffline(buf, (off, src) => {
            const conv = off.createConvolver(); conv.buffer = ir;
            const dry = off.createGain(), w = off.createGain(), mix = off.createGain();
            dry.gain.value = 1; w.gain.value = wet;
            src.connect(dry).connect(mix);
            src.connect(conv).connect(w).connect(mix);
            return mix;
        }, tail);
    }

    echo(buf) {
        return this.renderOffline(buf, (off, src) => {
            const dly = off.createDelay(1), fb = off.createGain(), w = off.createGain(), mix = off.createGain();
            dly.delayTime.value = 0.3; fb.gain.value = 0.38; w.gain.value = 0.45;
            src.connect(mix);
            src.connect(dly); dly.connect(fb); fb.connect(dly);
            dly.connect(w).connect(mix);
            return mix;
        }, 2.5);
    }

    telephone(buf) {
        const curve = new Float32Array(1024);
        for (let i = 0; i < 1024; i++) { const x = (i / 511.5) - 1; curve[i] = Math.tanh(x * 2.2) * 0.85; }
        return this.renderOffline(buf, (off, src) => {
            const shaper = off.createWaveShaper(); shaper.curve = curve;
            const out = off.createGain(); out.gain.value = 0.9;
            return this._chain(src, [
                this._biquad(off, 'highpass', 420), this._biquad(off, 'lowpass', 3100),
                this._biquad(off, 'peaking', 1800, 1.2, 4), shaper, out]);
        });
    }

    async polish(buf) {
        const out = await this.renderOffline(buf, (off, src) => {
            const comp = off.createDynamicsCompressor();
            comp.threshold.value = -26; comp.knee.value = 18; comp.ratio.value = 3;
            comp.attack.value = 0.01; comp.release.value = 0.22;
            return this._chain(src, [
                this._biquad(off, 'highpass', 80), this._biquad(off, 'peaking', 250, 1, -2.5),
                this._biquad(off, 'peaking', 3200, 0.9, 2.5), this._biquad(off, 'highshelf', 10000, 0.7, 2), comp]);
        });
        return this.matchLoudness(out, -16);
    }

    bakeEQ(buf) {
        const p = this.getEQ();
        return this.renderOffline(buf, (off, src) => this._chain(src, [
            this._biquad(off, 'lowshelf', p.low.freq, p.low.q, p.low.gain),
            this._biquad(off, 'peaking', p.mid.freq, p.mid.q, p.mid.gain),
            this._biquad(off, 'highshelf', p.high.freq, p.high.q, p.high.gain)]));
    }

    // ---------- analysis ----------
    _kWeight(x, sr) {
        const run = (data, b, a) => {
            const y = new Float64Array(data.length); let z1 = 0, z2 = 0;
            for (let i = 0; i < data.length; i++) {
                const v = data[i], o = b[0] * v + z1;
                z1 = b[1] * v - a[0] * o + z2; z2 = b[2] * v - a[1] * o; y[i] = o;
            }
            return y;
        };
        let f0 = 1681.974450955533, G = 3.999843853973347, Q = 0.7071752369554196;
        let K = Math.tan(Math.PI * f0 / sr);
        const Vh = Math.pow(10, G / 20), Vb = Math.pow(Vh, 0.4996667741545416);
        let a0 = 1 + K / Q + K * K;
        const s1 = run(x, [(Vh + Vb * K / Q + K * K) / a0, 2 * (K * K - Vh) / a0, (Vh - Vb * K / Q + K * K) / a0],
            [2 * (K * K - 1) / a0, (1 - K / Q + K * K) / a0]);
        f0 = 38.13547087602444; Q = 0.5003270373238773; K = Math.tan(Math.PI * f0 / sr); a0 = 1 + K / Q + K * K;
        return run(s1, [1, -2, 1], [2 * (K * K - 1) / a0, (1 - K / Q + K * K) / a0]);
    }

    // Integrated loudness (ITU-R BS.1770 style, with gating). Returns { lufs, peakDb }.
    measureLoudness(buf) {
        const sr = buf.sampleRate, len = buf.length;
        const P = new Float64Array(len + 1);
        let peak = 0;
        for (let c = 0; c < buf.numberOfChannels; c++) {
            const raw = buf.getChannelData(c);
            for (let i = 0; i < len; i++) { const a = Math.abs(raw[i]); if (a > peak) peak = a; }
            const k = this._kWeight(raw, sr);
            for (let i = 0; i < len; i++) P[i + 1] += k[i] * k[i];
        }
        // cumulative sum
        for (let i = 1; i <= len; i++) P[i] += P[i - 1];
        const block = Math.min(Math.floor(0.4 * sr), len), hop = Math.max(1, Math.floor(0.1 * sr));
        const ms = [];
        for (let s = 0; s + block <= len; s += hop) ms.push((P[s + block] - P[s]) / block);
        const L = (m) => -0.691 + 10 * Math.log10(m);
        const abs = ms.filter(m => m > 0 && L(m) > -70);
        let lufs = -Infinity;
        if (abs.length) {
            const rel = L(abs.reduce((a, b) => a + b, 0) / abs.length) - 10;
            const gated = abs.filter(m => L(m) > rel);
            if (gated.length) lufs = L(gated.reduce((a, b) => a + b, 0) / gated.length);
        }
        return { lufs, peakDb: peak > 0 ? 20 * Math.log10(peak) : -Infinity };
    }

    matchLoudness(buf, target) {
        const m = this.measureLoudness(buf);
        if (!isFinite(m.lufs)) return buf;
        return this._gain(buf, Math.pow(10, (target - m.lufs) / 20));
    }

    detectSilences(buf, thresholdDb, minMs) {
        const sr = buf.sampleRate, win = Math.max(1, Math.floor(sr * 0.01));
        const n = Math.floor(buf.length / win);
        if (!this._rms || this._rms.buf !== buf) {
            const rms = new Float32Array(n), ch = buf.numberOfChannels;
            const datas = []; for (let c = 0; c < ch; c++) datas.push(buf.getChannelData(c));
            for (let i = 0; i < n; i++) {
                let sum = 0; const s = i * win;
                for (let c = 0; c < ch; c++) { const d = datas[c]; for (let j = 0; j < win; j++) { const v = d[s + j]; sum += v * v; } }
                rms[i] = Math.sqrt(sum / (win * ch));
            }
            this._rms = { buf, rms };
        }
        const thr = Math.pow(10, thresholdDb / 20), rms = this._rms.rms, w = win / sr;
        const out = []; let run = -1;
        for (let i = 0; i <= n; i++) {
            const silent = i < n && rms[i] < thr;
            if (silent && run < 0) run = i;
            if (!silent && run >= 0) {
                if ((i - run) * w * 1000 >= minMs) out.push([run * w, i * w]);
                run = -1;
            }
        }
        return out;
    }

    // Shorten each silent region to keepMs (keeps natural pauses). Returns seconds saved.
    removeSilences(regions, keepMs) {
        const b = this.audioBuffer, sr = b.sampleRate, keep = keepMs / 1000;
        const cuts = [];
        for (const [s, e] of regions) if (e - s > keep + 0.01) cuts.push([Math.floor((s + keep / 2) * sr), Math.floor((e - keep / 2) * sr)]);
        if (!cuts.length) return 0;
        let removed = 0; for (const [s, e] of cuts) removed += e - s;
        const out = this.ctx.createBuffer(b.numberOfChannels, Math.max(1, b.length - removed), sr);
        for (let c = 0; c < b.numberOfChannels; c++) {
            const src = b.getChannelData(c), dst = out.getChannelData(c);
            let pos = 0, cur = 0;
            for (const [s, e] of cuts) { dst.set(src.subarray(cur, s), pos); pos += s - cur; cur = e; }
            dst.set(src.subarray(cur), pos);
        }
        this.audioBuffer = out;
        this.pauseOffset = 0;
        return removed / sr;
    }

    // =====================================================================
    // Live compressor / pan
    // =====================================================================
    applyComp() {
        const c = this.compCfg, now = this.ctx.currentTime;
        if (c.enabled) {
            this.comp.threshold.setValueAtTime(c.threshold, now); this.comp.ratio.setValueAtTime(c.ratio, now);
            this.comp.attack.setValueAtTime(c.attack / 1000, now); this.comp.release.setValueAtTime(c.release / 1000, now);
            this.comp.knee.setValueAtTime(c.knee, now); this.compMakeup.gain.setValueAtTime(Math.pow(10, c.makeup / 20), now);
        } else {
            this.comp.threshold.setValueAtTime(0, now); this.comp.ratio.setValueAtTime(1, now); this.comp.knee.setValueAtTime(0, now);
            this.compMakeup.gain.setValueAtTime(1, now);
        }
    }
    setComp(p) { Object.assign(this.compCfg, p); this.applyComp(); }
    getCompReduction() { const r = this.comp.reduction; return typeof r === 'number' ? r : (r ? r.value : 0); }
    setPan(v) { this.panner.pan.value = v; }

    bakeCompressor(buf) {
        const c = this.compCfg;
        return this.renderOffline(buf, (off, src) => {
            const comp = off.createDynamicsCompressor(), mk = off.createGain();
            comp.threshold.value = c.threshold; comp.ratio.value = c.ratio; comp.attack.value = c.attack / 1000;
            comp.release.value = c.release / 1000; comp.knee.value = c.knee; mk.gain.value = Math.pow(10, c.makeup / 20);
            src.connect(comp); comp.connect(mk);
            return mk;
        });
    }

    // =====================================================================
    // Clipboard and region editing
    // =====================================================================
    copy(a, b) { this.clipboard = this.extract(a, b); return this.clipboard.duration; }
    paste(at) {
        if (!this.clipboard || !this.audioBuffer) return false;
        this.audioBuffer = this.splice(at, at, this.clipboard);
        this.pauseOffset = 0;
        return true;
    }
    replaceRegion(a, b, buf) { this.audioBuffer = this.splice(a, b, buf); this.pauseOffset = 0; }
    silenceRegion(a, b) {
        const s = this._clampSample(a), e = this._clampSample(b);
        for (let c = 0; c < this.audioBuffer.numberOfChannels; c++) this.audioBuffer.getChannelData(c).fill(0, s, e);
    }
    insertSilence(at, sec) {
        const z = this.ctx.createBuffer(this.audioBuffer.numberOfChannels, Math.max(1, Math.floor(sec * this.audioBuffer.sampleRate)), this.audioBuffer.sampleRate);
        this.audioBuffer = this.splice(at, at, z);
        this.pauseOffset = 0;
    }

    // =====================================================================
    // Gain, limiter, gate
    // =====================================================================
    fxGain(buf, db) { return this._gain(buf, Math.pow(10, db / 20)); }

    // Look-ahead peak limiter: never lets the output exceed the ceiling
    async fxLimit(buf, ceilingDb = -1, releaseMs = 90) {
        const sr = buf.sampleRate, n = buf.length, ceil = Math.pow(10, ceilingDb / 20), la = Math.max(1, Math.floor(sr * 0.005));
        const chs = []; for (let c = 0; c < buf.numberOfChannels; c++) chs.push(buf.getChannelData(c));
        const g = new Float32Array(n);
        for (let i = 0; i < n; i++) { let p = 0; for (let c = 0; c < chs.length; c++) { const a = Math.abs(chs[c][i]); if (a > p) p = a; } g[i] = p > ceil ? ceil / p : 1; }
        // sliding minimum over the next `la` samples (monotonic deque)
        const m = new Float32Array(n), dq = new Int32Array(n + la + 2); let head = 0, tail = 0;
        for (let i = n - 1; i >= -la; i--) {
            if (i >= 0) { while (tail > head && g[dq[tail - 1]] >= g[i]) tail--; dq[tail++] = i; }
            const hi = i + la;
            if (i >= 0) { while (head < tail && dq[head] > hi) head++; m[i] = g[dq[head]]; }
            if ((i & 0x3ffff) === 0) await yieldUI();
        }
        const atk = 1 - Math.exp(-1 / (la / 3)), rel = 1 - Math.exp(-1 / (sr * releaseMs / 1000));
        let s = 1;
        for (let i = 0; i < n; i++) {
            s += (m[i] - s) * (m[i] < s ? atk : rel);
            if (s > 1) s = 1;
            for (let c = 0; c < chs.length; c++) { let v = chs[c][i] * s; if (v > ceil) v = ceil; else if (v < -ceil) v = -ceil; chs[c][i] = v; }
        }
        return buf;
    }

    async fxGate(buf, { thresholdDb = -45, floorDb = -50, attackMs = 4, releaseMs = 140, holdMs = 90 } = {}) {
        const sr = buf.sampleRate, n = buf.length, thr = Math.pow(10, thresholdDb / 20), floorG = Math.pow(10, floorDb / 20);
        const chs = []; for (let c = 0; c < buf.numberOfChannels; c++) chs.push(buf.getChannelData(c));
        const decay = Math.exp(-1 / (sr * 0.01)), look = Math.floor(sr * 0.006), hold = Math.floor(sr * holdMs / 1000);
        const open = new Uint8Array(n); let env = 0, holdLeft = 0;
        for (let i = 0; i < n; i++) {
            let p = 0; for (let c = 0; c < chs.length; c++) { const a = Math.abs(chs[c][i]); if (a > p) p = a; }
            env = p > env ? p : env * decay;
            if (env > thr) holdLeft = hold; else if (holdLeft > 0) holdLeft--;
            open[i] = env > thr || holdLeft > 0 ? 1 : 0;
            if ((i & 0x3ffff) === 0) await yieldUI();
        }
        const atk = 1 - Math.exp(-1 / (sr * attackMs / 1000)), rel = 1 - Math.exp(-1 / (sr * releaseMs / 1000));
        let gs = open[0] ? 1 : floorG;
        for (let i = 0; i < n; i++) {
            const target = open[Math.min(n - 1, i + look)] ? 1 : floorG;
            gs += (target - gs) * (target > gs ? atk : rel);
            for (let c = 0; c < chs.length; c++) chs[c][i] *= gs;
        }
        return buf;
    }

    // =====================================================================
    // Repair: noise reduction, hum, clicks, de-esser
    // =====================================================================
    async _avgPower(x, N, H, fft, win, frameOk) {
        const len = x.length, K = Math.max(1, Math.floor((len - N) / H) + 1), half = N / 2 + 1;
        const acc = new Float64Array(half), re = new Float64Array(N), im = new Float64Array(N);
        let used = 0;
        for (let k = 0; k < K; k++) {
            if (frameOk && !frameOk(k)) continue;
            const s = k * H;
            for (let i = 0; i < N; i++) { re[i] = (s + i < len ? x[s + i] : 0) * win[i]; im[i] = 0; }
            fft.forward(re, im);
            for (let b = 0; b < half; b++) acc[b] += re[b] * re[b] + im[b] * im[b];
            used++;
            if ((k & 63) === 0) await yieldUI();
        }
        if (used) for (let b = 0; b < half; b++) acc[b] /= used;
        return acc;
    }

    // Remember what the noise sounds like (select a stretch of just noise first)
    async learnNoise(startSec, endSec) {
        const sub = this.extract(startSec, endSec);
        if (sub.length < 4096) throw new Error('Selection too short');
        const N = 2048, H = 512, fft = makeFFT(N), win = hannWin(N), power = [];
        for (let c = 0; c < sub.numberOfChannels; c++) power.push(await this._avgPower(sub.getChannelData(c), N, H, fft, win, null));
        this.noiseProfile = { power, channels: sub.numberOfChannels };
    }

    async fxNoiseReduce(buf, { strength = 0.6, useLearned = true } = {}) {
        const N = 2048, H = 512, fft = makeFFT(N), win = hannWin(N), half = N / 2 + 1;
        const out = this.ctx.createBuffer(buf.numberOfChannels, buf.length, buf.sampleRate);
        const alpha = 1 + 2.5 * strength, floorG = Math.pow(10, -(10 + 20 * strength) / 20);
        for (let c = 0; c < buf.numberOfChannels; c++) {
            const x = buf.getChannelData(c), len = x.length, y = out.getChannelData(c);
            let noise;
            if (useLearned && this.noiseProfile && this.noiseProfile.channels === buf.numberOfChannels) noise = this.noiseProfile.power[c];
            else { // no profile: assume the quietest 12% of the audio is just noise
                const K0 = Math.max(1, Math.floor((len - N) / H) + 1), en = new Float64Array(K0);
                for (let k = 0; k < K0; k++) { let sum = 0; const s = k * H; for (let i = 0; i < N && s + i < len; i++) sum += x[s + i] * x[s + i]; en[k] = sum; }
                const thr = Float64Array.from(en).sort()[Math.floor(K0 * 0.12)];
                noise = await this._avgPower(x, N, H, fft, win, (k) => en[k] <= thr);
            }
            const P = len + 2 * N, K = Math.floor((P - N) / H) + 1;
            const re = new Float64Array(N), im = new Float64Array(N), prev = new Float64Array(half).fill(1), g = new Float64Array(half), gs = new Float64Array(half);
            for (let k = 0; k < K; k++) {
                const s = k * H - N;
                for (let i = 0; i < N; i++) { const idx = s + i; re[i] = (idx >= 0 && idx < len ? x[idx] : 0) * win[i]; im[i] = 0; }
                fft.forward(re, im);
                for (let b = 0; b < half; b++) {
                    const p = re[b] * re[b] + im[b] * im[b], g2 = 1 - alpha * noise[b] / (p + 1e-18);
                    g[b] = g2 < floorG * floorG ? floorG : Math.sqrt(g2);
                }
                gs[0] = g[0]; gs[half - 1] = g[half - 1];
                for (let b = 1; b < half - 1; b++) gs[b] = (g[b - 1] + 2 * g[b] + g[b + 1]) / 4;
                for (let b = 0; b < half; b++) {
                    const v = gs[b] >= prev[b] ? gs[b] : 0.55 * prev[b] + 0.45 * gs[b];
                    prev[b] = v; re[b] *= v; im[b] *= v;
                    if (b > 0 && b < half - 1) { re[N - b] *= v; im[N - b] *= v; }
                }
                fft.inverse(re, im);
                for (let i = 0; i < N; i++) { const idx = s + i; if (idx >= 0 && idx < len) y[idx] += re[i] * win[i] / 1.5; }
                if ((k & 31) === 0) await yieldUI();
            }
        }
        return out;
    }

    fxHum(buf, baseHz = 50) {
        return this.renderOffline(buf, (off, src) => {
            const nodes = [];
            for (let h = 1; h * baseHz < buf.sampleRate / 2 * 0.9 && h <= 6; h++) nodes.push(this._biquad(off, 'notch', baseHz * h, 35));
            return this._chain(src, nodes);
        });
    }

    fxDeclick(buf) {
        let fixed = 0;
        for (let c = 0; c < buf.numberOfChannels; c++) {
            const x = buf.getChannelData(c), n = x.length, r = new Float32Array(n);
            for (let pass = 0; pass < 3; pass++) {
                for (let i = 1; i < n - 1; i++) r[i] = x[i] - (x[i - 1] + x[i + 1]) / 2;
                let avg = 0.002; const hits = [];
                for (let i = 1; i < n - 1; i++) {
                    const e = Math.abs(r[i]);
                    // a click is a sharp local peak far above the normal sample-to-sample wobble
                    if (e > 8 * avg + 0.03 && e >= Math.abs(r[i - 1]) && e >= Math.abs(r[i + 1])) hits.push(i);
                    else avg += (e - avg) * 0.0008;
                }
                for (const i of hits) { x[i] = (x[i - 1] + x[i + 1]) / 2; fixed++; }
                if (!hits.length) break;
            }
        }
        this.lastDeclick = fixed;
        return buf;
    }

    async fxDeEss(buf, amount = 0.5) {
        const split = (type) => this.renderOffline(buf, (off, src) =>
            this._chain(src, [this._biquad(off, type, 6000, 0.7071), this._biquad(off, type, 6000, 0.7071)]));
        const [lo, hi] = [await split('lowpass'), await split('highpass')];
        const sr = buf.sampleRate, n = buf.length, ch = buf.numberOfChannels;
        const thr = Math.pow(10, (-22 - 20 * amount) / 20), ratio = 4 + 8 * amount;
        const atk = 1 - Math.exp(-1 / (sr * 0.002)), rel = 1 - Math.exp(-1 / (sr * 0.06));
        const out = this.ctx.createBuffer(ch, n, sr);
        const H = [], Lw = [], O = [];
        for (let c = 0; c < ch; c++) { H.push(hi.getChannelData(c)); Lw.push(lo.getChannelData(c)); O.push(out.getChannelData(c)); }
        let env = 0;
        for (let i = 0; i < n; i++) {
            let p = 0; for (let c = 0; c < ch; c++) { const a = Math.abs(H[c][i]); if (a > p) p = a; }
            env += (p - env) * (p > env ? atk : rel);
            const gain = env > thr ? Math.pow(thr / env, 1 - 1 / ratio) : 1;
            for (let c = 0; c < ch; c++) O[c][i] = Lw[c][i] + H[c][i] * gain;
            if ((i & 0x3ffff) === 0) await yieldUI();
        }
        return out;
    }

    // =====================================================================
    // Time stretch and pitch shift (WSOLA: keeps voices natural)
    // =====================================================================
    async fxTimeStretch(buf, ratio) { // ratio 1.25 = 25% longer (slower), same pitch
        if (Math.abs(ratio - 1) < 0.001) return buf;
        const sr = buf.sampleRate, ch = buf.numberOfChannels, len = buf.length;
        const N = 2 * Math.round(sr * 0.046 / 2), Hs = N / 2, Ha = Hs / ratio, delta = Math.floor(N / 4), D = 4;
        const win = hannWin(N);
        const mono = new Float32Array(len);
        for (let c = 0; c < ch; c++) { const d = buf.getChannelData(c); for (let i = 0; i < len; i++) mono[i] += d[i] / ch; }
        const dl = Math.floor(len / D), dec = new Float32Array(dl);
        for (let i = 0; i < dl; i++) { let a = 0; for (let k = 0; k < D; k++) a += mono[i * D + k]; dec[i] = a / D; }

        const outLen = Math.max(1, Math.round(len * ratio)), out = this.ctx.createBuffer(ch, outLen, sr);
        const outs = []; for (let c = 0; c < ch; c++) outs.push(out.getChannelData(c));
        const ins = []; for (let c = 0; c < ch; c++) ins.push(buf.getChannelData(c));
        const frames = Math.ceil(outLen / Hs) + 1;
        let prevPos = 0;
        for (let k = 0; k < frames; k++) {
            let pos;
            if (k === 0) pos = 0;
            else {
                const nominal = Math.round(k * Ha), natural = prevPos + Hs;
                // coarse search on the decimated signal, then refine at full rate
                const tgt = Math.floor(natural / D), L = Math.floor(Hs / D);
                let best = nominal, bestScore = -Infinity;
                const lo = Math.floor((nominal - delta) / D), hi = Math.floor((nominal + delta) / D);
                for (let cand = lo; cand <= hi; cand++) {
                    if (cand < 0 || cand + L >= dl || tgt + L >= dl) continue;
                    let sc = 0; for (let i = 0; i < L; i += 2) sc += dec[cand + i] * dec[tgt + i];
                    if (sc > bestScore) { bestScore = sc; best = cand * D; }
                }
                let best2 = best, score2 = -Infinity;
                for (let cand = best - D; cand <= best + D; cand++) {
                    if (cand < 0 || cand + Hs >= len || natural + Hs >= len) continue;
                    let sc = 0; for (let i = 0; i < Hs; i += 3) sc += mono[cand + i] * mono[natural + i];
                    if (sc > score2) { score2 = sc; best2 = cand; }
                }
                pos = best2;
            }
            const o = k * Hs;
            for (let c = 0; c < ch; c++) {
                const x = ins[c], y = outs[c];
                for (let i = 0; i < N; i++) {
                    const oi = o + i, ii = pos + i;
                    if (oi >= outLen) break;
                    if (ii < len) y[oi] += x[ii] * win[i];
                }
            }
            prevPos = pos;
            if ((k & 15) === 0) await yieldUI();
        }
        return out;
    }

    async fxPitchShift(buf, semitones) {
        const f = Math.pow(2, semitones / 12);
        if (Math.abs(f - 1) < 0.0005) return buf;
        const stretched = await this.fxTimeStretch(buf, f); // longer by f, same pitch
        return this.fxResample(stretched, f);                // back to the original length, pitch x f
    }

    // =====================================================================
    // Stereo tools
    // =====================================================================
    fxMono(buf) {
        const ch = buf.numberOfChannels; if (ch < 2) return buf;
        const n = buf.length, mix = new Float32Array(n);
        for (let c = 0; c < ch; c++) { const d = buf.getChannelData(c); for (let i = 0; i < n; i++) mix[i] += d[i] / ch; }
        for (let c = 0; c < ch; c++) buf.getChannelData(c).set(mix);
        return buf;
    }
    fxSwap(buf) {
        if (buf.numberOfChannels < 2) return buf;
        const l = buf.getChannelData(0), r = buf.getChannelData(1), t = Float32Array.from(l);
        l.set(r); r.set(t);
        return buf;
    }
    fxMidSide(buf, { mid = 1, side = 1 }) { // width: side>1 widens, side=0 is mono; mid=0 keeps only what differs between L and R
        if (buf.numberOfChannels < 2) return buf;
        const l = buf.getChannelData(0), r = buf.getChannelData(1);
        for (let i = 0; i < l.length; i++) {
            const m = (l[i] + r[i]) / 2 * mid, s = (l[i] - r[i]) / 2 * side;
            l[i] = m + s; r[i] = m - s;
        }
        return buf;
    }
    fxRemoveVocals(buf) { return this.fxMidSide(buf, { mid: 0, side: 1.4 }); }   // centre-panned vocals cancel out
    fxIsolateVocals(buf) { return this.fxMidSide(buf, { mid: 1.2, side: 0 }); }   // keep only the centre

    // =====================================================================
    // Music bed with auto-ducking
    // =====================================================================
    // Gain curve (one value per 10 ms) that dips whenever the voice is speaking
    duckCurve(buf, o) {
        const sr = buf.sampleRate, win = Math.max(1, Math.floor(sr * 0.01)), F = Math.ceil(buf.length / win), ch = buf.numberOfChannels;
        const thr = Math.pow(10, o.thresholdDb / 20), speaking = new Uint8Array(F);
        for (let f = 0; f < F; f++) {
            let sum = 0, cnt = 0; const s = f * win, e = Math.min(buf.length, s + win);
            for (let c = 0; c < ch; c++) { const d = buf.getChannelData(c); for (let i = s; i < e; i++) { sum += d[i] * d[i]; cnt++; } }
            speaking[f] = Math.sqrt(sum / Math.max(1, cnt)) > thr ? 1 : 0;
        }
        const hang = 15, look = 5, low = Math.pow(10, -o.duckDb / 20), g = new Float32Array(F);
        const ca = 1 - Math.exp(-10 / 60), cr = 1 - Math.exp(-10 / Math.max(20, o.releaseMs));
        let cur = 1, hangLeft = 0;
        for (let f = 0; f < F; f++) {
            if (speaking[Math.min(F - 1, f + look)]) hangLeft = hang; else if (hangLeft > 0) hangLeft--;
            const target = hangLeft > 0 ? low : 1;
            cur += (target - cur) * (target < cur ? ca : cr);
            g[f] = cur;
        }
        return { g, win: win / sr };
    }

    mixMusic(music, o) {
        const b = this.audioBuffer, sr = b.sampleRate, n = b.length, ch = b.numberOfChannels;
        const duck = o.duckDb > 0 ? this.duckCurve(b, o) : null, winS = Math.max(1, Math.floor(sr * 0.01));
        const out = this.ctx.createBuffer(ch, n, sr);
        const gain = Math.pow(10, o.gainDb / 20), start = Math.floor(o.startSec * sr), mlen = music.length;
        const span = o.loop ? Math.max(0, n - start) : Math.max(0, Math.min(mlen, n - start));
        const fi = Math.floor(o.fadeIn * sr), fo = Math.floor(o.fadeOut * sr);
        for (let c = 0; c < ch; c++) {
            const src = b.getChannelData(c), dst = out.getChannelData(c), m = music.getChannelData(Math.min(c, music.numberOfChannels - 1));
            for (let i = 0; i < n; i++) {
                let v = src[i]; const j = i - start;
                if (j >= 0 && j < span) {
                    let gg = gain;
                    if (duck) { const f = Math.floor(i / winS), fr = (i - f * winS) / winS; gg *= duck.g[f] * (1 - fr) + duck.g[Math.min(duck.g.length - 1, f + 1)] * fr; }
                    if (fi && j < fi) gg *= j / fi;
                    if (fo && j > span - fo) gg *= (span - j) / fo;
                    v += m[o.loop ? j % mlen : j] * gg;
                }
                const a = Math.abs(v);
                dst[i] = a > 0.9 ? Math.sign(v) * (0.9 + 0.1 * Math.tanh((a - 0.9) / 0.1)) : v;
            }
        }
        this.audioBuffer = out;
        this.pauseOffset = 0;
    }

    // =====================================================================
    // Analysis: tempo and key
    // =====================================================================
    async detectTempo(buf) {
        const sr = buf.sampleRate, ch = buf.numberOfChannels, maxN = Math.min(buf.length, Math.floor(sr * 90));
        const hop = Math.max(1, Math.floor(sr * 0.005)), F = Math.floor(maxN / hop);
        if (F < 400) return null;
        const env = new Float32Array(F);
        for (let f = 0; f < F; f++) {
            let sum = 0; const s = f * hop;
            for (let c = 0; c < ch; c++) { const d = buf.getChannelData(c); for (let i = 0; i < hop; i++) { const v = d[s + i]; sum += v * v; } }
            env[f] = Math.log(1 + 1000 * Math.sqrt(sum / (hop * ch)));
        }
        const flux = new Float32Array(F);
        for (let f = 1; f < F; f++) flux[f] = Math.max(0, env[f] - env[f - 1]);
        let mean = 0; for (let f = 0; f < F; f++) mean += flux[f]; mean /= F;
        for (let f = 0; f < F; f++) flux[f] = Math.max(0, flux[f] - mean);
        const fps = sr / hop, minLag = Math.floor(fps * 60 / 200), maxLag = Math.ceil(fps * 60 / 60), ac = new Float64Array(maxLag + 2);
        for (let lag = minLag - 1; lag <= maxLag + 1; lag++) { let s = 0; for (let f = 0; f + lag < F; f++) s += flux[f] * flux[f + lag]; ac[lag] = s / (F - lag); }
        let best = minLag, bs = -1;
        for (let lag = minLag; lag <= maxLag; lag++) {
            const bpm = 60 * fps / lag, prior = Math.exp(-Math.pow(Math.log2(bpm / 110), 2) / 1.6);
            const sc = (ac[lag] + 0.5 * (ac[lag * 2] || 0) * 0) * prior;
            if (sc > bs) { bs = sc; best = lag; }
        }
        const y0 = ac[best - 1], y1 = ac[best], y2 = ac[best + 1], den = y0 - 2 * y1 + y2;
        const shift = den !== 0 ? 0.5 * (y0 - y2) / den : 0;
        let ac0 = 0; for (let f = 0; f < F; f++) ac0 += flux[f] * flux[f];
        ac0 /= F;
        const strength = ac0 > 1e-6 ? ac[best] / ac0 : 0;
        if (strength < 0.35) return null; // no steady pulse (speech, ambience, a held note)
        return { bpm: 60 * fps / (best + shift), strength };
    }

    async detectKey(buf) {
        const sr = buf.sampleRate, ch = buf.numberOfChannels, N = 8192, fft = makeFFT(N), win = hannWin(N);
        const total = Math.min(buf.length, Math.floor(sr * 100)), hopS = Math.floor(sr * 0.5), chroma = new Float64Array(12);
        const re = new Float64Array(N), im = new Float64Array(N);
        for (let s = 0, k = 0; s + N <= total; s += hopS, k++) {
            for (let i = 0; i < N; i++) { let v = 0; for (let c = 0; c < ch; c++) v += buf.getChannelData(c)[s + i]; re[i] = v / ch * win[i]; im[i] = 0; }
            fft.forward(re, im);
            for (let b = 1; b < N / 2; b++) {
                const f = b * sr / N; if (f < 65 || f > 2100) continue;
                const mag = Math.sqrt(re[b] * re[b] + im[b] * im[b]);
                const midi = 69 + 12 * Math.log2(f / 440), pc = ((Math.round(midi) % 12) + 12) % 12;
                chroma[pc] += mag;
            }
            if ((k & 7) === 0) await yieldUI();
        }
        const sum = chroma.reduce((a, b) => a + b, 0); if (sum <= 0) return null;
        const maj = [6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88];
        const min = [6.33, 2.68, 3.52, 5.38, 2.60, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17];
        const corr = (a, b) => { const ma = a.reduce((x, y) => x + y, 0) / 12, mb = b.reduce((x, y) => x + y, 0) / 12; let n = 0, da = 0, db = 0; for (let i = 0; i < 12; i++) { n += (a[i] - ma) * (b[i] - mb); da += (a[i] - ma) ** 2; db += (b[i] - mb) ** 2; } return n / Math.sqrt(da * db); };
        const names = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
        let best = { score: -2 };
        for (let t = 0; t < 12; t++) {
            const rot = Array.from({ length: 12 }, (_, i) => chroma[(i + t) % 12]);
            const cM = corr(rot, maj), cm = corr(rot, min);
            if (cM > best.score) best = { score: cM, name: names[t] + ' major' };
            if (cm > best.score) best = { score: cm, name: names[t] + ' minor' };
        }
        return { key: best.name, confidence: best.score };
    }

    // =====================================================================
    // Export encoders
    // =====================================================================
    encodeWAV(buf, bits = 16) {
        const ch = buf.numberOfChannels, n = buf.length, bytes = bits / 8, dataLen = n * ch * bytes;
        const ab = new ArrayBuffer(44 + dataLen), v = new DataView(ab);
        let pos = 0;
        const u16 = (d) => { v.setUint16(pos, d, true); pos += 2; }, u32 = (d) => { v.setUint32(pos, d, true); pos += 4; };
        u32(0x46464952); u32(36 + dataLen); u32(0x45564157); u32(0x20746d66); u32(16);
        u16(bits === 32 ? 3 : 1); u16(ch); u32(buf.sampleRate); u32(buf.sampleRate * ch * bytes); u16(ch * bytes); u16(bits);
        u32(0x61746164); u32(dataLen);
        const data = []; for (let c = 0; c < ch; c++) data.push(buf.getChannelData(c));
        for (let i = 0; i < n; i++) {
            for (let c = 0; c < ch; c++) {
                const x = Math.max(-1, Math.min(1, data[c][i]));
                if (bits === 16) { v.setInt16(pos, (x < 0 ? x * 32768 : x * 32767) | 0, true); pos += 2; }
                else if (bits === 24) { const q = Math.round(x < 0 ? x * 8388608 : x * 8388607); v.setUint8(pos, q & 255); v.setUint8(pos + 1, (q >> 8) & 255); v.setUint8(pos + 2, (q >> 16) & 255); pos += 3; }
                else { v.setFloat32(pos, data[c][i], true); pos += 4; }
            }
        }
        return new Blob([ab], { type: 'audio/wav' });
    }

    async encodeMP3(buf, kbps = 192) {
        if (!window.lamejs) {
            await new Promise((res, rej) => {
                const sc = document.createElement('script');
                sc.src = 'https://cdnjs.cloudflare.com/ajax/libs/lamejs/1.2.1/lame.min.js';
                sc.onload = res; sc.onerror = () => rej(new Error('Could not load the MP3 encoder. Check your internet connection.'));
                document.head.appendChild(sc);
            });
        }
        const ch = Math.min(2, buf.numberOfChannels), enc = new window.lamejs.Mp3Encoder(ch, buf.sampleRate, kbps), block = 1152, parts = [];
        const toI16 = (f) => { const a = new Int16Array(f.length); for (let i = 0; i < f.length; i++) { const x = Math.max(-1, Math.min(1, f[i])); a[i] = x < 0 ? x * 32768 : x * 32767; } return a; };
        const L = toI16(buf.getChannelData(0)), R = ch > 1 ? toI16(buf.getChannelData(1)) : null;
        for (let i = 0, k = 0; i < L.length; i += block, k++) {
            const chunk = ch > 1 ? enc.encodeBuffer(L.subarray(i, i + block), R.subarray(i, i + block)) : enc.encodeBuffer(L.subarray(i, i + block));
            if (chunk.length) parts.push(new Int8Array(chunk));
            if ((k & 127) === 0) await yieldUI();
        }
        const end = enc.flush(); if (end.length) parts.push(new Int8Array(end));
        return new Blob(parts, { type: 'audio/mpeg' });
    }

    // =====================================================================
    // Music mastering and the built-in demo song
    // =====================================================================
    // One-click master for songs: tidy lows, add air, glue compression, loudness to -14 LUFS, safe peaks
    async masterMusic(buf) {
        const out = await this.renderOffline(buf, (off, src) => {
            const comp = off.createDynamicsCompressor();
            comp.threshold.value = -20; comp.knee.value = 12; comp.ratio.value = 2.2; comp.attack.value = 0.03; comp.release.value = 0.25;
            return this._chain(src, [
                this._biquad(off, 'highpass', 28, 0.7), this._biquad(off, 'lowshelf', 90, 0.7, 1.5),
                this._biquad(off, 'peaking', 320, 1, -1.5), this._biquad(off, 'peaking', 3000, 0.8, 1),
                this._biquad(off, 'highshelf', 9500, 0.7, 2.5), comp]);
        });
        this.matchLoudness(out, -14);
        return this.fxLimit(out, -1);
    }

    // Mastering with a preset. `amount` (0..1) scales how much EQ and compression is applied.
    async masterWith(buf, p, amount = 1) {
        const ceiling = p.ceiling === undefined ? -1 : p.ceiling;
        if (p.voice) return this.fxLimit(await this.polish(buf), ceiling);
        const a = Math.max(0, Math.min(1, amount)), cm = p.comp * a;
        const out = await this.renderOffline(buf, (off, src) => {
            const comp = off.createDynamicsCompressor();
            comp.threshold.value = -10 - 14 * cm; comp.knee.value = 12; comp.ratio.value = 1 + 3.2 * cm; comp.attack.value = 0.03; comp.release.value = 0.25;
            return this._chain(src, [
                this._biquad(off, 'highpass', 28, 0.7), this._biquad(off, 'lowshelf', p.low[0], 0.7, p.low[1] * a),
                this._biquad(off, 'peaking', 320, 1, p.mud * a), this._biquad(off, 'peaking', 3000, 0.8, p.pres * a),
                this._biquad(off, 'highshelf', p.air[0], 0.7, p.air[1] * a), comp]);
        });
        if (p.width && p.width !== 1 && out.numberOfChannels > 1) this.fxMidSide(out, { mid: 1, side: 1 + (p.width - 1) * a });
        this.matchLoudness(out, p.target);
        await this.fxLimit(out, ceiling);
        // the limiter shaves a little loudness off, so nudge back up to the stated target (twice at most)
        for (let i = 0; i < 2; i++) {
            const m = this.measureLoudness(out);
            if (!isFinite(m.lufs) || Math.abs(m.lufs - p.target) < 0.4) break;
            this._gain(out, Math.pow(10, (p.target - m.lufs) / 20));
            await this.fxLimit(out, ceiling);
        }
        return out;
    }

    // A short synthesized song (drums, bass, pads, plucks) so first-time visitors can hear the editor straight away
    async makeDemo() {
        const sr = this.ctx.sampleRate, bpm = 100, beat = 60 / bpm, bars = 8, len = bars * 4 * beat + 1.6;
        const off = new OfflineAudioContext(2, Math.ceil(len * sr), sr);
        const master = off.createGain(); master.gain.value = 0.8; master.connect(off.destination);
        const noise = off.createBuffer(1, sr, sr), nd = noise.getChannelData(0);
        let seed = 12345; for (let i = 0; i < nd.length; i++) { seed = (seed * 1664525 + 1013904223) >>> 0; nd[i] = seed / 2147483648 - 1; }
        const env = (g, t, a, d, peak) => { g.gain.setValueAtTime(0.0001, t); g.gain.linearRampToValueAtTime(peak, t + a); g.gain.exponentialRampToValueAtTime(0.0001, t + a + d); };
        const pan = (node, p) => { const sp = off.createStereoPanner(); sp.pan.value = p; node.connect(sp); sp.connect(master); };
        const hit = (t, type, v = 1) => {
            if (type === 'kick') {
                const o = off.createOscillator(), g = off.createGain();
                o.frequency.setValueAtTime(165, t); o.frequency.exponentialRampToValueAtTime(42, t + 0.14);
                env(g, t, 0.002, 0.34, 0.95 * v); o.connect(g); g.connect(master); o.start(t); o.stop(t + 0.45);
            } else if (type === 'snare') {
                const n = off.createBufferSource(), f = this._biquad(off, 'bandpass', 1900, 0.8), g = off.createGain(), o = off.createOscillator(), og = off.createGain();
                n.buffer = noise; env(g, t, 0.001, 0.17, 0.55 * v); n.connect(f); f.connect(g); pan(g, 0.05); n.start(t); n.stop(t + 0.3);
                o.type = 'triangle'; o.frequency.setValueAtTime(190, t); env(og, t, 0.001, 0.1, 0.3 * v); o.connect(og); og.connect(master); o.start(t); o.stop(t + 0.2);
            } else {
                const n = off.createBufferSource(), f = this._biquad(off, 'highpass', 7500, 0.7), g = off.createGain();
                n.buffer = noise; env(g, t, 0.001, 0.045, 0.2 * v); n.connect(f); f.connect(g); pan(g, 0.25); n.start(t, Math.random() * 0.5); n.stop(t + 0.1);
            }
        };
        const tone = (t, f, durS, type, peak, lp, p) => {
            const o = off.createOscillator(), g = off.createGain(), l = this._biquad(off, 'lowpass', lp, 2);
            o.type = type; o.frequency.value = f; env(g, t, 0.012, durS, peak); o.connect(l); l.connect(g); pan(g, p); o.start(t); o.stop(t + durS + 0.05);
        };
        const chords = [[220, 261.63, 329.63], [174.61, 220, 261.63], [261.63, 329.63, 392], [196, 246.94, 293.66]];
        const roots = [55, 43.65, 65.41, 49];
        for (let b = 0; b < bars; b++) {
            const bt = b * 4 * beat, ci = Math.floor(b / 2), chord = chords[ci];
            [0, 2].forEach((k) => hit(bt + k * beat, 'kick'));
            if (b % 2) hit(bt + 2.5 * beat, 'kick', 0.8);
            [1, 3].forEach((k) => hit(bt + k * beat, 'snare'));
            for (let i = 0; i < 8; i++) hit(bt + i * beat / 2, 'hat', i % 2 ? 0.55 : 1);
            [0, 1.5, 2, 3].forEach((k) => tone(bt + k * beat, roots[ci], beat * 0.8, 'sawtooth', 0.38, 420, 0));
            if (b % 2 === 0) { // pads on chord changes
                chord.forEach((f, i) => [-7, 7].forEach((c) => {
                    const o = off.createOscillator(), g = off.createGain(), l = this._biquad(off, 'lowpass', 1500, 0.7), t0 = bt, dur = 8 * beat;
                    o.type = 'sawtooth'; o.frequency.value = f * 2; o.detune.value = c;
                    g.gain.setValueAtTime(0.0001, t0); g.gain.linearRampToValueAtTime(0.045, t0 + 0.6); g.gain.setValueAtTime(0.045, t0 + dur - 0.5); g.gain.linearRampToValueAtTime(0.0001, t0 + dur);
                    o.connect(l); l.connect(g); pan(g, (i - 1) * 0.45); o.start(t0); o.stop(t0 + dur + 0.05);
                }));
            }
            if (b >= 4) for (let i = 0; i < 8; i++) tone(bt + i * beat / 2, chord[[0, 1, 2, 1][i % 4]] * 2, 0.33, 'triangle', 0.17, 3500, i % 2 ? 0.5 : -0.5);
        }
        const buf = await off.startRendering();
        let pk = 0; for (let c = 0; c < 2; c++) { const d = buf.getChannelData(c); for (let i = 0; i < d.length; i++) pk = Math.max(pk, Math.abs(d[i])); }
        const g = pk > 0 ? 0.89 / pk : 1;
        for (let c = 0; c < 2; c++) { const d = buf.getChannelData(c); for (let i = 0; i < d.length; i++) d[i] *= g; }
        return this.fxFadeOut(buf, 1.2);
    }

    // ---------- basic edits ----------
    // Add a song to the end. With crossfade > 0 the two songs overlap: the old one fades out
    // while the new one fades in (equal-power by default, so there is no dip in loudness).
    appendAudio(newBuffer, { crossfade = 0, curve = 'equal', matchLoudness = false } = {}) {
        if (!this.audioBuffer) { this.audioBuffer = this.cloneBuffer(newBuffer); return { joinStart: 0, overlap: 0 }; }
        const a = this.audioBuffer, sr = a.sampleRate;
        let b = newBuffer;
        if (matchLoudness) { // bring the new song to the same loudness as what is already there
            const la = this.measureLoudness(a).lufs, lb = this.measureLoudness(b).lufs;
            if (isFinite(la) && isFinite(lb)) { b = this.cloneBuffer(b); this._gain(b, Math.max(0.125, Math.min(8, Math.pow(10, (la - lb) / 20)))); }
        }
        const ov = Math.max(0, Math.min(Math.floor(crossfade * sr), Math.floor(a.length * 0.9), Math.floor(b.length * 0.9)));
        const channels = Math.max(a.numberOfChannels, b.numberOfChannels), joinAt = a.length - ov;
        const out = this.ctx.createBuffer(channels, a.length + b.length - ov, sr);
        for (let c = 0; c < channels; c++) {
            const d = out.getChannelData(c), da = a.getChannelData(Math.min(c, a.numberOfChannels - 1)), db = b.getChannelData(Math.min(c, b.numberOfChannels - 1));
            d.set(da.subarray(0, joinAt), 0);
            for (let i = 0; i < ov; i++) {
                const t = (i + 0.5) / ov;
                const gOut = curve === 'linear' ? 1 - t : Math.cos(t * Math.PI / 2), gIn = curve === 'linear' ? t : Math.sin(t * Math.PI / 2);
                d[joinAt + i] = da[joinAt + i] * gOut + db[i] * gIn;
            }
            d.set(db.subarray(ov), a.length);
        }
        this.audioBuffer = out;
        this.pauseOffset = Math.max(0, joinAt / sr - 3); // park the playhead just before the join so you can hear it
        return { joinStart: joinAt / sr, overlap: ov / sr };
    }

    trim(startSec, endSec) {
        if (!this.audioBuffer) return;
        const s = this._clampSample(startSec), e = this._clampSample(endSec);
        if (e - s <= 0) return;
        const out = this.ctx.createBuffer(this.audioBuffer.numberOfChannels, e - s, this.audioBuffer.sampleRate);
        for (let c = 0; c < out.numberOfChannels; c++) out.getChannelData(c).set(this.audioBuffer.getChannelData(c).subarray(s, e));
        this.audioBuffer = out;
        this.pauseOffset = 0;
    }

    cut(startSec, endSec) {
        if (!this.audioBuffer) return;
        const s = this._clampSample(startSec), e = this._clampSample(endSec);
        const newLen = this.audioBuffer.length - (e - s);
        if (e - s <= 0 || newLen <= 0) return;
        const out = this.ctx.createBuffer(this.audioBuffer.numberOfChannels, newLen, this.audioBuffer.sampleRate);
        for (let c = 0; c < out.numberOfChannels; c++) {
            const src = this.audioBuffer.getChannelData(c), dst = out.getChannelData(c);
            dst.set(src.subarray(0, s), 0);
            dst.set(src.subarray(e), s);
        }
        this.audioBuffer = out;
        this.pauseOffset = 0;
    }

    exportWAV() {
        if (!this.audioBuffer) return null;
        const numOfChan = this.audioBuffer.numberOfChannels;
        const length = this.audioBuffer.length * numOfChan * 2;
        const buffer = new ArrayBuffer(44 + length);
        const view = new DataView(buffer);
        const channels = [];
        let offset = 0, pos = 0;
        const u16 = (d) => { view.setUint16(pos, d, true); pos += 2; };
        const u32 = (d) => { view.setUint32(pos, d, true); pos += 4; };
        u32(0x46464952); u32(36 + length); u32(0x45564157);
        u32(0x20746d66); u32(16); u16(1); u16(numOfChan);
        u32(this.audioBuffer.sampleRate); u32(this.audioBuffer.sampleRate * 2 * numOfChan);
        u16(numOfChan * 2); u16(16);
        u32(0x61746164); u32(length);
        for (let i = 0; i < numOfChan; i++) channels.push(this.audioBuffer.getChannelData(i));
        while (offset < this.audioBuffer.length) {
            for (let i = 0; i < numOfChan; i++) {
                let s = Math.max(-1, Math.min(1, channels[i][offset]));
                s = (s < 0 ? s * 32768 : s * 32767) | 0;
                view.setInt16(pos, s, true); pos += 2;
            }
            offset++;
        }
        return new Blob([buffer], { type: 'audio/wav' });
    }
}

const store = new AudioStore();
const $ = (id) => document.getElementById(id);
// Theme colours for everything drawn on a canvas (refreshed whenever the theme changes)
const TC = {};
function readTheme() {
    const cs = getComputedStyle(document.documentElement), g = (n) => cs.getPropertyValue(n).trim();
    TC.teal = g('--teal'); TC.ice = g('--ice'); TC.amber = g('--amber'); TC.amberLight = g('--amber-light'); TC.rose = g('--rose');
    ['teal', 'ice', 'amber', 'rose'].forEach((k) => { TC['rgb_' + k] = g('--rgb-' + k).replace(/\s+/g, ','); });
}
readTheme();
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

// =====================================================================
// Elements
// =====================================================================
const fileInput = $('audio-input'), mergeInput = $('merge-input');
const playPauseBtn = $('play-pause-btn'), playIcon = $('play-icon');
const stopBtn = $('stop-btn'), startBtn = $('start-btn'), loopBtn = $('loop-btn');
const timeDisplay = $('time-display'), durationDisplay = $('duration-display');
const volumeSlider = $('volume-slider'), fileList = $('file-list');
const undoBtn = $('nav-edit');

const stageBody = $('stage-body'), container = $('waveform-container');
const canvas = $('waveform-canvas'), playedCanvas = $('waveform-played'), rulerCanvas = $('ruler-canvas');
const progressClip = $('progress-clip'), playhead = $('playhead');
const selectionOverlay = $('selection-overlay'), selectionBadge = $('selection-badge'), selectionHint = $('selection-hint');
const hoverLine = $('hover-line'), hoverTime = $('hover-time');
const markerLayer = $('marker-layer'), silenceLayer = $('silence-layer');
const overview = $('overview'), overviewCanvas = $('overview-canvas'), overviewWindow = $('overview-window'), overviewHead = $('overview-head');
const scopeChip = $('scope-chip');
const liveCanvas = $('live-canvas');
const isMac = /Mac|iPhone|iPad/.test(navigator.platform);
$('palette-kbd').textContent = isMac ? '\u2318K' : 'Ctrl K';

// =====================================================================
// State
// =====================================================================
let view = { start: 0, end: 1 };
let sel = null;            // { a, b } seconds
let markers = [];          // seconds, sorted
let silences = [];         // [[start, end]]
let waveStyle = 'bars';    // 'bars' | 'smooth' | 'live' | 'spectro'
let activeTab = 'mixer';
let analysisDirty = true;
let loudTarget = -16;
let assets = [];

const D = () => store.getDuration();
const span = () => view.end - view.start;
const frac = (t) => (t - view.start) / span();
const timeAt = (f) => view.start + f * span();

// =====================================================================
// Small UI helpers
// =====================================================================
let actionToast = null;
function toast(message, type = 'ok', opts = {}) {
    const el = document.createElement('div');
    el.className = `toast ${type === 'error' ? 'error' : ''}`;
    el.innerHTML = `<span class="material-symbols-rounded">${type === 'error' ? 'error' : 'check_circle'}</span><span class="toast-text"></span>`;
    el.querySelector('.toast-text').textContent = message;
    if (opts.action) {
        // only one "Undo" toast at a time, so it always means the latest edit
        if (actionToast) actionToast.remove();
        actionToast = el;
        el.classList.add('has-action');
        const b = document.createElement('button');
        b.className = 'toast-action';
        b.innerHTML = `<span class="material-symbols-rounded">${opts.action.icon || 'undo'}</span>${opts.action.label}`;
        b.addEventListener('click', () => { el.remove(); opts.action.run(); });
        el.appendChild(b);
    }
    $('toast-stack').appendChild(el);
    setTimeout(() => { el.classList.add('leaving'); setTimeout(() => el.remove(), 260); }, opts.duration || (opts.action ? 7000 : 2800));
}

async function withBusy(text, fn) {
    const el = document.createElement('div');
    el.className = 'toast busy';
    el.innerHTML = '<span class="material-symbols-rounded">progress_activity</span><span></span>';
    el.lastElementChild.textContent = text;
    $('toast-stack').appendChild(el);
    await new Promise(r => setTimeout(r, 30)); // let the toast paint first
    try { return await fn(); } finally { el.remove(); }
}

function openModal({ title, message = '', input = null, confirmLabel = 'Confirm', danger = false }) {
    return new Promise((resolve) => {
        const modal = $('modal'), field = $('modal-input'), ok = $('modal-ok'), cancel = $('modal-cancel');
        $('modal-title').textContent = title;
        $('modal-message').textContent = message;
        $('modal-message').style.display = message ? '' : 'none';
        ok.textContent = confirmLabel;
        ok.classList.toggle('danger', danger);
        field.hidden = input === null;
        if (input !== null) field.value = input;
        modal.hidden = false;
        (input !== null ? field : ok).focus();
        if (input !== null) field.select();
        const close = (result) => {
            modal.hidden = true;
            ok.removeEventListener('click', onOk); cancel.removeEventListener('click', onCancel);
            modal.removeEventListener('mousedown', onBackdrop); document.removeEventListener('keydown', onKey, true);
            resolve(result);
        };
        const onOk = () => close(input !== null ? field.value : true);
        const onCancel = () => close(input !== null ? null : false);
        const onBackdrop = (e) => { if (e.target === modal) onCancel(); };
        const onKey = (e) => {
            if (e.key === 'Escape') { e.stopPropagation(); onCancel(); }
            if (e.key === 'Enter') { e.stopPropagation(); e.preventDefault(); onOk(); }
        };
        ok.addEventListener('click', onOk); cancel.addEventListener('click', onCancel);
        modal.addEventListener('mousedown', onBackdrop); document.addEventListener('keydown', onKey, true);
    });
}

function fmtTime(seconds, decimals = 2) {
    seconds = Math.max(0, seconds);
    const m = Math.floor(seconds / 60).toString().padStart(2, '0');
    const s = Math.floor(seconds % 60).toString().padStart(2, '0');
    const f = Math.floor((seconds % 1) * Math.pow(10, decimals)).toString().padStart(decimals, '0');
    return `${m}:${s}.${f}`;
}
const updateTimeDisplay = (s) => { timeDisplay.innerText = fmtTime(s); };
function setSliderFill(input) {
    input.style.setProperty('--fill', ((input.value - input.min) / (input.max - input.min)) * 100 + '%');
}

// =====================================================================
// Enable / disable
// =====================================================================
const gatedButtons = () => document.querySelectorAll('.tool-btn, .tile, .polish-card, #match-btn, #sil-apply, #eq-apply, #zoom-in, #zoom-out, #zoom-fit, .needs-audio');
function setHasAudio(has) {
    document.body.classList.toggle('has-audio', has);
    [playPauseBtn, stopBtn, startBtn].forEach(b => { b.disabled = !has; });
    gatedButtons().forEach(b => { b.disabled = !has; });
    refreshUndo();
}
function refreshUndo() {
    const has = !!store.audioBuffer, tl = has ? store.getTimeline() : { past: [], future: [] };
    undoBtn.disabled = !(has && store.canUndo());
    $('nav-redo').disabled = !(has && store.canRedo());
    $('hist-undo').disabled = undoBtn.disabled; $('hist-redo').disabled = $('nav-redo').disabled;
    const badge = $('undo-count');
    badge.hidden = tl.past.length === 0; badge.textContent = tl.past.length;
    undoBtn.title = tl.past.length ? `Undo: ${tl.past[tl.past.length - 1]}` : 'Undo (Ctrl/Cmd + Z)';
    $('nav-redo').title = tl.future.length ? `Redo: ${tl.future[0]}` : 'Redo (Ctrl/Cmd + Shift + Z)';
    renderHistory(tl);
    if ($('hs-edits')) { $('hs-edits').textContent = tl.past.length; $('hs-undo').textContent = tl.past.length; $('hs-redo').textContent = tl.future.length; }
}

// ---- History timeline: click any step to travel to it ----
function renderHistory(tl) {
    const list = $('history-list'); list.innerHTML = '';
    if (!store.audioBuffer) { list.innerHTML = '<li class="pal-empty">Edits will appear here.</li>'; return; }
    const N = tl.past.length, entries = [{ label: 'Start of session', kind: N === 0 ? 'current' : 'past' }];
    tl.past.forEach((l, j) => entries.push({ label: l, kind: j + 1 === N ? 'current' : 'past' }));
    tl.future.forEach((l) => entries.push({ label: l, kind: 'future' }));
    entries.forEach((en, k) => {
        const li = document.createElement('li');
        li.className = `hist-item ${en.kind}`;
        li.innerHTML = '<span class="hist-dot"></span><span class="hist-label"></span>' + (en.kind === 'current' ? '<span class="hist-tag">now</span>' : en.kind === 'future' ? '<span class="hist-tag">undone</span>' : '');
        li.querySelector('.hist-label').textContent = en.label;
        li.addEventListener('click', () => travelTo(k, N));
        list.appendChild(li);
    });
    const cur = list.querySelector('.current'); if (cur) cur.scrollIntoView({ block: 'nearest' });
}
function travelTo(k, N) {
    if (k === N) return;
    const prevLen = store.audioBuffer.length;
    let buf = null, meta = markerMeta();
    if (k < N) for (let i = 0; i < N - k; i++) { buf = store.undo(meta); meta = store.restoredMeta || meta; }
    else for (let i = 0; i < k - N; i++) { buf = store.redo(meta); meta = store.restoredMeta || meta; }
    if (buf) restoreAfterTravel(prevLen, k < N ? 'Went back in history' : 'Went forward in history');
}

// =====================================================================
// Assets panel
// =====================================================================
function renderAssets() {
    if (!assets.length) { fileList.innerHTML = '<li class="file-item empty-state">No audio loaded yet</li>'; return; }
    fileList.innerHTML = '';
    assets.forEach((a) => {
        const li = document.createElement('li');
        li.className = 'file-item' + (a.appended ? ' appended' : '');
        li.innerHTML = `<span class="material-symbols-rounded">${a.appended ? 'merge_type' : 'audio_file'}</span>
            <span class="file-text"><span class="file-name"></span><span class="file-tag">${a.appended ? 'Appended' : 'Main track'}</span></span>`;
        li.querySelector('.file-name').textContent = a.name;
        li.title = a.name;
        fileList.appendChild(li);
    });
}
function updateStats() {
    const info = store.getInfo();
    $('stat-duration').textContent = info ? fmtTime(info.duration, 1) : '--';
    $('stat-rate').textContent = info ? (info.sampleRate / 1000).toFixed(1) + ' kHz' : '--';
    $('stat-channels').textContent = info ? (info.channels === 1 ? 'Mono' : info.channels === 2 ? 'Stereo' : info.channels + ' ch') : '--';
    durationDisplay.textContent = 'of ' + fmtTime(info ? info.duration : 0);
}

// =====================================================================
// View window (zoom + pan)
// =====================================================================
let viewAnim = null;
function updateZoomLabel() {
    const d = D(), z = d ? d / span() : 1;
    $('zoom-fit').textContent = (z < 10 ? Math.round(z * 100) : Math.round(z) * 100) + '%';
    if (d) {
        // minus and "fit" have nothing to do when the whole track is already showing
        $('zoom-out').disabled = z < 1.02;
        $('zoom-in').disabled = span() <= Math.min(0.02, d) * 1.05;
    }
}
function clampView(start, end) {
    const d = D(), sp = clamp(end - start, Math.min(0.02, d), d), st = clamp(start, 0, d - sp);
    return { start: st, end: st + sp };
}
// Instant (used by scroll wheel, minimap drag)
function setView(start, end) {
    const d = D(); if (!d) return;
    cancelAnimationFrame(viewAnim);
    const v = clampView(start, end); view.start = v.start; view.end = v.end;
    updateZoomLabel(); scheduleDraw();
}
// Smooth (used by the zoom buttons so you can see what happened)
function animateView(start, end) {
    const d = D(); if (!d) return;
    const to = clampView(start, end), from = { start: view.start, end: view.end }, t0 = performance.now(), dur = 240;
    cancelAnimationFrame(viewAnim);
    const step = (now) => {
        const k = clamp((now - t0) / dur, 0, 1), e = 1 - Math.pow(1 - k, 3);
        view.start = from.start + (to.start - from.start) * e; view.end = from.end + (to.end - from.end) * e;
        updateZoomLabel(); scheduleDraw();
        if (k < 1) viewAnim = requestAnimationFrame(step);
    };
    viewAnim = requestAnimationFrame(step);
}
const fitView = () => animateView(0, D());
function zoomAround(factor, t) { // instant, anchored under the cursor
    const sp = span(), f = (t - view.start) / sp, nsp = sp * factor;
    setView(t - f * nsp, t - f * nsp + nsp);
}
function zoomButton(factor) { // animated, anchored sensibly
    if (!store.audioBuffer) return;
    const sp = span(), mid = (view.start + view.end) / 2, t = store.getCurrentTime();
    let anchor = mid;
    if (factor < 1) {
        if (sel && sel.b - sel.a > 0.05) {
            // with a selection, the first press zooms right onto it
            const len = sel.b - sel.a;
            if (sp > len * 1.25) { animateView(sel.a - len * 0.1, sel.b + len * 0.1); return; }
            anchor = (sel.a + sel.b) / 2;
        } else if (store.isPlaying || (t > view.start + sp * 0.05 && t < view.end - sp * 0.05)) anchor = t;
    }
    const nsp = sp * factor, f = (anchor - view.start) / sp;
    animateView(anchor - f * nsp, anchor - f * nsp + nsp);
}
$('zoom-in').addEventListener('click', () => zoomButton(0.5));
$('zoom-out').addEventListener('click', () => zoomButton(2));
$('zoom-fit').addEventListener('click', () => {
    if (!store.audioBuffer) return;
    if (span() < D() * 0.999) fitView();
    else if (sel && sel.b - sel.a > 0.05) { const len = sel.b - sel.a; animateView(sel.a - len * 0.1, sel.b + len * 0.1); }
    else toast('Already showing the whole track. Use + or scroll over the waveform to zoom in.');
});
$('zoom-fit').title = 'Fit the whole track (0). With a selection, zooms onto it.';

// =====================================================================
// Drawing: peaks, waveform, spectrogram, ruler, overview
// =====================================================================
let drawPending = false;
function scheduleDraw() {
    if (drawPending) return;
    drawPending = true;
    requestAnimationFrame(() => { drawPending = false; drawAll(); });
}

function sizeCanvas(c, w, h, dpr) {
    const W = Math.max(1, Math.floor(w * dpr)), H = Math.max(1, Math.floor(h * dpr));
    if (c.width !== W) c.width = W;
    if (c.height !== H) c.height = H;
}

function computePeaks(buffer, t0, t1, cols) {
    const sr = buffer.sampleRate;
    const s0 = clamp(Math.floor(t0 * sr), 0, buffer.length - 1), s1 = clamp(Math.ceil(t1 * sr), s0 + 1, buffer.length);
    const ch0 = buffer.getChannelData(0), ch1 = buffer.numberOfChannels > 1 ? buffer.getChannelData(1) : null;
    const peaks = new Float32Array(cols * 2), step = (s1 - s0) / cols;
    for (let i = 0; i < cols; i++) {
        const a = s0 + Math.floor(i * step), b = Math.max(a + 1, Math.min(s1, s0 + Math.floor((i + 1) * step)));
        const stride = Math.max(1, Math.floor((b - a) / 256));
        let min = 1, max = -1;
        for (let j = a; j < b; j += stride) {
            const x = ch0[j]; if (x < min) min = x; if (x > max) max = x;
            if (ch1) { const y = ch1[j]; if (y < min) min = y; if (y > max) max = y; }
        }
        if (min > max) { min = 0; max = 0; }
        peaks[i * 2] = min; peaks[i * 2 + 1] = max;
    }
    return peaks;
}

function paintWave(c, peaks, cols, colors, style, dpr) {
    const g = c.getContext('2d'), w = c.width, h = c.height, mid = h / 2;
    g.clearRect(0, 0, w, h);
    const grad = g.createLinearGradient(0, 0, 0, h);
    grad.addColorStop(0, colors[0]); grad.addColorStop(0.5, colors[1]); grad.addColorStop(1, colors[0]);
    g.fillStyle = grad;
    const amp = mid * 0.92;
    if (style === 'bars') {
        const barW = 2 * dpr, pitch = 3 * dpr, n = Math.floor(w / pitch);
        for (let i = 0; i < n; i++) {
            const idx = Math.min(cols - 1, Math.floor((i / n) * cols));
            const a = Math.max(Math.abs(peaks[idx * 2]), Math.abs(peaks[idx * 2 + 1]));
            const bh = Math.max(2 * dpr, a * amp * 2);
            g.beginPath();
            if (g.roundRect) g.roundRect(i * pitch, mid - bh / 2, barW, bh, barW / 2); else g.rect(i * pitch, mid - bh / 2, barW, bh);
            g.fill();
        }
    } else {
        g.beginPath();
        for (let i = 0; i < cols; i++) { const x = (i / cols) * w, y = mid - Math.max(peaks[i * 2 + 1], 0.002) * amp; i ? g.lineTo(x, y) : g.moveTo(x, y); }
        for (let i = cols - 1; i >= 0; i--) g.lineTo((i / cols) * w, mid - Math.min(peaks[i * 2], -0.002) * amp);
        g.closePath(); g.fill();
    }
}

// ---- Spectrogram (offline FFT of the visible window) ----
const SP_N = 1024;
const spWin = new Float32Array(SP_N), spCos = new Float64Array(SP_N / 2), spSin = new Float64Array(SP_N / 2), spRev = new Uint16Array(SP_N);
for (let i = 0; i < SP_N; i++) spWin[i] = 0.5 - 0.5 * Math.cos((2 * Math.PI * i) / (SP_N - 1));
for (let k = 0; k < SP_N / 2; k++) { spCos[k] = Math.cos((2 * Math.PI * k) / SP_N); spSin[k] = Math.sin((2 * Math.PI * k) / SP_N); }
for (let i = 0; i < SP_N; i++) { let r = 0, x = i; for (let b = 0; b < 10; b++) { r = (r << 1) | (x & 1); x >>= 1; } spRev[i] = r; }
function fft(re, im) {
    for (let i = 0; i < SP_N; i++) { const j = spRev[i]; if (j > i) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
    for (let size = 2; size <= SP_N; size <<= 1) {
        const half = size >> 1, tstep = SP_N / size;
        for (let i = 0; i < SP_N; i += size) {
            for (let j = 0, k = 0; j < half; j++, k += tstep) {
                const a = i + j, b = a + half;
                const tr = re[b] * spCos[k] + im[b] * spSin[k], ti = im[b] * spCos[k] - re[b] * spSin[k];
                re[b] = re[a] - tr; im[b] = im[a] - ti; re[a] += tr; im[a] += ti;
            }
        }
    }
}
const spLUT = (() => {
    const stops = [[0, [14, 16, 19]], [0.2, [28, 22, 80]], [0.4, [106, 42, 140]], [0.6, [212, 69, 122]], [0.8, [255, 181, 71]], [1, [255, 244, 214]]];
    const lut = new Uint8ClampedArray(256 * 3);
    for (let i = 0; i < 256; i++) {
        const t = i / 255; let k = 0; while (k < stops.length - 2 && t > stops[k + 1][0]) k++;
        const [t0, c0] = stops[k], [t1, c1] = stops[k + 1], f = clamp((t - t0) / (t1 - t0), 0, 1);
        for (let c = 0; c < 3; c++) lut[i * 3 + c] = c0[c] + (c1[c] - c0[c]) * f;
    }
    return lut;
})();
const spCanvas = document.createElement('canvas');
function paintSpectrogram(c, buf, t0, t1, dpr) {
    const cols = clamp(Math.floor(c.width / (2 * dpr)), 50, 700), rows = clamp(Math.floor(c.height / (2 * dpr)), 40, 220);
    spCanvas.width = cols; spCanvas.height = rows;
    const sctx = spCanvas.getContext('2d'), img = sctx.createImageData(cols, rows);
    const sr = buf.sampleRate, fmin = 40, fmax = Math.min(16000, sr / 2 * 0.98);
    const rowBin = new Float32Array(rows);
    for (let r = 0; r < rows; r++) rowBin[r] = (fmin * Math.pow(fmax / fmin, 1 - r / (rows - 1))) / (sr / SP_N);
    const chs = []; for (let k = 0; k < buf.numberOfChannels; k++) chs.push(buf.getChannelData(k));
    const re = new Float64Array(SP_N), im = new Float64Array(SP_N), db = new Float32Array(SP_N / 2 + 1);
    for (let i = 0; i < cols; i++) {
        const start = Math.round((t0 + ((i + 0.5) / cols) * (t1 - t0)) * sr - SP_N / 2);
        for (let k = 0; k < SP_N; k++) {
            const idx = start + k; let v = 0;
            if (idx >= 0 && idx < buf.length) { for (let q = 0; q < chs.length; q++) v += chs[q][idx]; v /= chs.length; }
            re[k] = v * spWin[k]; im[k] = 0;
        }
        fft(re, im);
        for (let k = 0; k <= SP_N / 2; k++) db[k] = 20 * Math.log10(Math.sqrt(re[k] * re[k] + im[k] * im[k]) / (SP_N / 4) + 1e-9);
        for (let r = 0; r < rows; r++) {
            const b = rowBin[r], i0 = Math.floor(b), f = b - i0;
            const v = db[i0] * (1 - f) + db[Math.min(i0 + 1, SP_N / 2)] * f;
            const li = Math.floor(clamp((v + 95) / 80, 0, 1) * 255) * 3, p = (r * cols + i) * 4;
            img.data[p] = spLUT[li]; img.data[p + 1] = spLUT[li + 1]; img.data[p + 2] = spLUT[li + 2]; img.data[p + 3] = 255;
        }
    }
    sctx.putImageData(img, 0, 0);
    const g = c.getContext('2d');
    g.clearRect(0, 0, c.width, c.height);
    g.imageSmoothingEnabled = true; g.imageSmoothingQuality = 'high';
    g.drawImage(spCanvas, 0, 0, c.width, c.height);
    g.font = `500 ${10 * dpr}px "JetBrains Mono", monospace`; g.textBaseline = 'middle';
    [[100, '100 Hz'], [1000, '1 kHz'], [10000, '10 kHz']].forEach(([f, label]) => {
        if (f < fmin || f > fmax) return;
        const y = (1 - Math.log(f / fmin) / Math.log(fmax / fmin)) * c.height;
        g.strokeStyle = 'rgba(255,255,255,0.12)'; g.lineWidth = dpr; g.setLineDash([3 * dpr, 4 * dpr]);
        g.beginPath(); g.moveTo(0, y); g.lineTo(c.width, y); g.stroke(); g.setLineDash([]);
        g.fillStyle = 'rgba(236,239,244,0.75)'; g.fillText(label, 8 * dpr, y - 8 * dpr);
    });
}

function drawRuler() {
    const dpr = window.devicePixelRatio || 1, w = rulerCanvas.clientWidth, h = rulerCanvas.clientHeight;
    if (w <= 0) return;
    sizeCanvas(rulerCanvas, w, h, dpr);
    const g = rulerCanvas.getContext('2d');
    g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
    if (!D()) return;
    const steps = [0.01, 0.02, 0.05, 0.1, 0.25, 0.5, 1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 1800];
    const pxPerSec = w / span();
    const major = steps.find(s => s * pxPerSec >= 90) || steps[steps.length - 1], minor = major / 5;
    g.font = '500 10px "JetBrains Mono", monospace'; g.textBaseline = 'middle';
    const firstIdx = Math.floor(view.start / minor), lastIdx = Math.ceil(view.end / minor);
    for (let idx = firstIdx; idx <= lastIdx; idx++) {
        const t = Math.round(idx * minor * 1e4) / 1e4; // avoid 1.9999999 style drift
        if (t < 0) continue;
        const x = Math.round((t - view.start) * pxPerSec) + 0.5;
        const isMajor = idx % 5 === 0;
        g.strokeStyle = isMajor ? '#4a5262' : '#2f3643';
        g.beginPath(); g.moveTo(x, h); g.lineTo(x, isMajor ? h - 12 : h - 6); g.stroke();
        if (isMajor) {
            const label = major < 1 ? `${Math.floor(t / 60)}:${(Math.round((t % 60) * 100) / 100).toFixed(major < 0.1 ? 2 : 1).padStart(major < 0.1 ? 5 : 4, '0')}`
                : `${Math.floor(t / 60)}:${Math.floor(Math.round(t % 60 * 1000) / 1000).toString().padStart(2, '0')}`;
            g.fillStyle = '#7b8494'; g.fillText(label, x + 5, h / 2 - 3);
        }
    }
}

function drawAll() {
    const buf = store.audioBuffer; if (!buf) return;
    const dpr = window.devicePixelRatio || 1, w = container.clientWidth, h = container.clientHeight;
    if (w <= 0 || h <= 0) return;
    sizeCanvas(canvas, w, h, dpr); sizeCanvas(playedCanvas, w, h, dpr);
    playedCanvas.style.width = w + 'px';
    container.classList.toggle('spectro', waveStyle === 'spectro');
    container.classList.toggle('live', waveStyle === 'live');
    if (waveStyle === 'spectro') {
        paintSpectrogram(canvas, buf, view.start, view.end, dpr);
    } else {
        const cols = Math.max(1, Math.min(canvas.width, 1600));
        const peaks = computePeaks(buf, view.start, view.end, cols);
        const shape = waveStyle === 'live' ? 'bars' : waveStyle;
        paintWave(canvas, peaks, cols, [TC.ice, TC.teal], shape, dpr);
        paintWave(playedCanvas, peaks, cols, [TC.amberLight, TC.amber], shape, dpr);
    }
    drawRuler();
    renderOverlays();
}

function drawOverview() {
    const buf = store.audioBuffer; if (!buf) return;
    const dpr = window.devicePixelRatio || 1, w = overview.clientWidth, h = overview.clientHeight;
    if (w <= 0) return;
    sizeCanvas(overviewCanvas, w, h, dpr);
    const cols = Math.min(overviewCanvas.width, 1600), peaks = computePeaks(buf, 0, buf.duration, cols);
    const g = overviewCanvas.getContext('2d'), W = overviewCanvas.width, H = overviewCanvas.height, mid = H / 2;
    g.clearRect(0, 0, W, H);
    g.fillStyle = `rgba(${TC.rgb_ice},0.55)`;
    g.beginPath();
    for (let i = 0; i < cols; i++) { const x = (i / cols) * W, y = mid - Math.max(peaks[i * 2 + 1], 0.003) * mid * 0.8; i ? g.lineTo(x, y) : g.moveTo(x, y); }
    for (let i = cols - 1; i >= 0; i--) g.lineTo((i / cols) * W, mid - Math.min(peaks[i * 2], -0.003) * mid * 0.8);
    g.closePath(); g.fill();
}

function bufferChanged(keepView = false) {
    cancelAnimationFrame(viewAnim);
    if (!keepView) { view.start = 0; view.end = D() || 1; }
    else setViewNow();
    updateZoomLabel(); updateStats(); drawOverview(); scheduleDraw(); markAnalysisDirty();
    if (typeof onBufferChanged === 'function') onBufferChanged();
}
function setViewNow() { const d = D(); view.end = Math.min(view.end, d); view.start = Math.min(view.start, Math.max(0, view.end - Math.min(0.02, d))); if (view.end <= view.start) { view.start = 0; view.end = d; } }

window.addEventListener('resize', () => {
    if (store.audioBuffer) { drawOverview(); scheduleDraw(); }
});

// =====================================================================
// Overlays: playhead, selection, markers, silences, overview window
// =====================================================================
function setProgress(t) {
    const f = frac(t);
    playhead.style.left = `${f * 100}%`;
    playhead.style.display = f >= 0 && f <= 1 ? 'block' : 'none';
    progressClip.style.width = `${clamp(f, 0, 1) * 100}%`;
    overviewHead.style.left = `${D() ? (t / D()) * 100 : 0}%`;
}

function renderSelection() {
    if (!sel) {
        selectionOverlay.style.display = 'none';
        selectionHint.textContent = store.audioBuffer ? 'Drag to select. Double-click a phrase.' : 'Drag to select a region';
        selectionHint.classList.remove('has-selection');
        scopeChip.textContent = 'Whole track'; scopeChip.classList.remove('is-selection');
        if (typeof updateScopeNotes === 'function') updateScopeNotes();
        return;
    }
    const fa = frac(sel.a), fb = frac(sel.b);
    if (fb < 0 || fa > 1) selectionOverlay.style.display = 'none';
    else {
        selectionOverlay.style.display = 'block';
        const l = Math.max(0, fa), r = Math.min(1, fb);
        selectionOverlay.style.left = `${l * 100}%`; selectionOverlay.style.width = `${(r - l) * 100}%`;
    }
    selectionBadge.textContent = `${(sel.b - sel.a).toFixed(2)}s`;
    selectionHint.textContent = `${fmtTime(sel.a)}  to  ${fmtTime(sel.b)}`;
    selectionHint.classList.add('has-selection');
    scopeChip.textContent = `Selection \u00b7 ${(sel.b - sel.a).toFixed(1)}s`; scopeChip.classList.add('is-selection');
    if (typeof updateScopeNotes === 'function') updateScopeNotes();
}
function clearSelection() { sel = null; renderSelection(); }

function renderMarkers() {
    markerLayer.innerHTML = '';
    markers.forEach((mk, i) => {
        const t = mk.t, f = frac(t); if (f < 0 || f > 1) return;
        const m = document.createElement('div'); m.className = 'marker'; m.style.left = `${f * 100}%`;
        const flag = document.createElement('button');
        flag.className = 'marker-flag'; flag.textContent = mk.name ? `${i + 1}  ${mk.name}` : i + 1;
        flag.title = `${mk.name || 'Marker ' + (i + 1)} at ${fmtTime(t)}. Click to jump, double-click to rename, right-click to remove.`;
        flag.addEventListener('click', (e) => { e.stopPropagation(); seekTo(t); });
        flag.addEventListener('dblclick', async (e) => {
            e.stopPropagation();
            const name = await openModal({ title: 'Name this marker', message: 'Named markers become chapters when you export.', input: mk.name || '', confirmLabel: 'Save name' });
            if (name !== null) { mk.name = name.trim(); renderMarkers(); }
        });
        flag.addEventListener('contextmenu', (e) => { e.preventDefault(); markers.splice(i, 1); renderMarkers(); toast('Marker removed'); });
        m.appendChild(flag); markerLayer.appendChild(m);
    });
}

function renderSilences() {
    silenceLayer.innerHTML = '';
    if (activeTab !== 'analyze') return;
    silences.forEach(([s, e]) => {
        const fa = frac(s), fb = frac(e); if (fb < 0 || fa > 1) return;
        const l = Math.max(0, fa), r = Math.min(1, fb), d = document.createElement('div');
        d.className = 'silence-band'; d.style.left = `${l * 100}%`; d.style.width = `${Math.max(0.2, (r - l) * 100)}%`;
        silenceLayer.appendChild(d);
    });
}

function renderOverlays() {
    renderSelection(); renderMarkers(); renderSilences();
    if (typeof renderSubs === 'function') renderSubs();
    if (typeof drawBeatGrid === 'function') drawBeatGrid();
    if (typeof drawDuck === 'function') drawDuck();
    setProgress(store.getCurrentTime());
    if (D()) {
        overviewWindow.style.left = `${(view.start / D()) * 100}%`;
        overviewWindow.style.width = `${(span() / D()) * 100}%`;
    }
}

// =====================================================================
// Mouse interaction on the waveform
// =====================================================================
let dragging = false, moved = false, anchor = 0;
const fracFromEvent = (e) => { const r = container.getBoundingClientRect(); return clamp((e.clientX - r.left) / r.width, 0, 1); };

function seekTo(t) {
    if (!sel) store.region = null;
    store.seek(t);
    if (!store.isPlaying) { /* keep paused */ }
    if (t < view.start || t > view.end) setView(t - span() * 0.1, t - span() * 0.1 + span());
    setProgress(t); updateTimeDisplay(t);
}

container.addEventListener('mousedown', (e) => {
    if (!store.audioBuffer || e.button !== 0) return;
    dragging = true; moved = false; anchor = timeAt(fracFromEvent(e));
});
window.addEventListener('mousemove', (e) => {
    if (!store.audioBuffer) return;
    const r = container.getBoundingClientRect();
    const inside = e.clientX >= r.left && e.clientX <= r.right && e.clientY >= r.top && e.clientY <= r.bottom;
    if (inside && !dragging) {
        const f = fracFromEvent(e);
        hoverLine.style.display = 'block'; hoverLine.style.left = `${f * 100}%`;
        hoverLine.classList.toggle('flip', f > 0.9);
        hoverTime.textContent = fmtTime(timeAt(f));
    } else hoverLine.style.display = 'none';
    if (!dragging) return;
    const t = timeAt(fracFromEvent(e));
    if (Math.abs(frac(t) - frac(anchor)) * r.width > 4) moved = true;
    if (moved) { sel = { a: Math.min(anchor, t), b: Math.max(anchor, t) }; renderSelection(); }
});
window.addEventListener('mouseup', () => {
    if (!dragging) return;
    dragging = false;
    if (!moved) { clearSelection(); seekTo(anchor); }
});
container.addEventListener('mouseleave', () => { hoverLine.style.display = 'none'; });

// Double-click selects the whole spoken phrase (the stretch between two silences)
function selectPhraseAt(t) {
    if (!store.audioBuffer) return;
    const sil = store.detectSilences(store.audioBuffer, -45, 220);
    let a = 0, b = D();
    for (const [s, e] of sil) {
        if (e <= t) a = e;
        else if (s >= t) { b = s; break; }
        else { toast('That spot is silence. Try double-clicking on sound.', 'error'); return; }
    }
    if (b - a < 0.05) return;
    sel = { a, b }; renderSelection();
    toast(`Phrase selected (${(b - a).toFixed(1)}s). Cut, trim or add an effect.`);
}
container.addEventListener('dblclick', (e) => { if (store.audioBuffer) selectPhraseAt(timeAt(fracFromEvent(e))); });

// Scroll to zoom (around the cursor), sideways scroll to pan
stageBody.addEventListener('wheel', (e) => {
    if (!store.audioBuffer) return;
    e.preventDefault();
    const r = container.getBoundingClientRect();
    if (Math.abs(e.deltaX) > Math.abs(e.deltaY)) {
        const dt = (e.deltaX / r.width) * span(); setView(view.start + dt, view.end + dt);
    } else {
        const t = timeAt(clamp((e.clientX - r.left) / r.width, 0, 1));
        zoomAround(Math.exp(e.deltaY * (e.ctrlKey ? 0.01 : 0.0018)), t);
    }
}, { passive: false });

// Minimap: drag the window or click to jump
let ovDrag = null;
function ovMove(e) {
    const r = overview.getBoundingClientRect(), t = clamp((e.clientX - r.left) / r.width, 0, 1) * D(), sp = span();
    setView(t - ovDrag.offset, t - ovDrag.offset + sp);
}
overview.addEventListener('pointerdown', (e) => {
    if (!store.audioBuffer) return;
    overview.setPointerCapture(e.pointerId);
    const r = overview.getBoundingClientRect(), t = clamp((e.clientX - r.left) / r.width, 0, 1) * D();
    ovDrag = { offset: t >= view.start && t <= view.end ? t - view.start : span() / 2 };
    ovMove(e);
});
overview.addEventListener('pointermove', (e) => { if (ovDrag) ovMove(e); });
overview.addEventListener('pointerup', () => { ovDrag = null; });

// =====================================================================
// Playback, meters, ambient glow
// =====================================================================
function togglePlayPause() {
    if (!store.audioBuffer) return;
    if (store.isPlaying) { store.pause(); playIcon.innerText = 'play_arrow'; playPauseBtn.classList.remove('is-playing'); }
    else {
        // with a selection, play (or loop) just that part
        const r = sel && sel.b - sel.a >= 0.05 ? { a: sel.a, b: sel.b } : null;
        store.region = r;
        if (r && (store.pauseOffset < r.a || store.pauseOffset >= r.b)) store.pauseOffset = r.a;
        store.play(); playIcon.innerText = 'pause'; playPauseBtn.classList.add('is-playing');
    }
}
function resetPlayState(keepPosition = false) {
    if (keepPosition === true) { // a selection finished playing: stay at its start
        setProgress(store.pauseOffset); updateTimeDisplay(store.pauseOffset);
    } else { store.region = null; store.stop(); setProgress(0); updateTimeDisplay(0); }
    playIcon.innerText = 'play_arrow'; playPauseBtn.classList.remove('is-playing');
}
store.onEnded = (wasRegion) => resetPlayState(!!wasRegion);

const meterEls = { l: $('meter-l').firstElementChild, r: $('meter-r').firstElementChild, vox: $('meter-vox').firstElementChild };
const meterState = { l: 0, r: 0, vox: 0 };
const toMeter = (p) => p <= 0.00001 ? 0 : clamp((20 * Math.log10(p) + 54) / 54, 0, 1);
function updateMeters() {
    const lv = store.isPlaying ? store.getLevels() : { l: 0, r: 0, vox: 0 };
    for (const k of ['l', 'r', 'vox']) {
        const target = toMeter(lv[k]);
        meterState[k] = target > meterState[k] ? target : Math.max(0, meterState[k] - 0.025);
        meterEls[k].style.clipPath = `inset(${(1 - meterState[k]) * 100}% 0 0 0)`;
    }
}

const logoRects = [...$('logo-mark').querySelectorAll('rect')];
const bandEdges = [[1, 4], [4, 12], [12, 40], [40, 140], [140, 450]];
const bands = [0, 0, 0, 0, 0];
let ambient = 0;
function updateAmbient() {
    const spec = store.getSpectrum();
    let total = 0;
    bandEdges.forEach(([a, b], i) => {
        let s = 0; for (let k = a; k < b; k++) s += spec[k];
        bands[i] = bands[i] * 0.55 + (s / (b - a) / 255) * 0.45; total += bands[i];
        logoRects[i].style.transform = `scaleY(${(0.5 + Math.min(1, bands[i] * 1.5) * 1.2).toFixed(3)})`;
    });
    // simple beat detector: a bass spike well above its recent average
    let bass = 0; for (let k = 1; k < 8; k++) bass += spec[k]; bass /= 7 * 255;
    live.bassAvg = live.bassAvg * 0.96 + bass * 0.04;
    if (store.isPlaying && live.cool <= 0 && bass > live.bassAvg * 1.28 + 0.06) { live.beat = 1; live.cool = 9; }
    live.cool--; live.beat *= 0.9;
    ambient = ambient * 0.85 + Math.min(1, (total / 5) * 1.6 + live.beat * 0.25) * 0.15;
    document.documentElement.style.setProperty('--level', ambient.toFixed(3));
    return spec;
}

// ---- Live moving waves: ribbons that breathe with each band, a real oscilloscope line, spectrum bars ----
const live = { phase: 0, beat: 0, cool: 0, bassAvg: 0, last: 0, peaks: new Float32Array(64) };
const RIBBONS = [
    { band: 0, c: 'teal', freq: 1.1, speed: 0.9, amp: 0.62 },
    { band: 1, c: 'ice', freq: 1.9, speed: -1.25, amp: 0.5 },
    { band: 3, c: 'amber', freq: 3.1, speed: 1.7, amp: 0.4 },
    { band: 4, c: 'rose', freq: 4.8, speed: -2.3, amp: 0.3 }
];
function drawLive(ts, spec) {
    const dpr = window.devicePixelRatio || 1, w = container.clientWidth, h = container.clientHeight;
    if (w <= 0 || h <= 0) return;
    sizeCanvas(liveCanvas, w, h, dpr);
    const g = liveCanvas.getContext('2d'), W = liveCanvas.width, H = liveCanvas.height, mid = H / 2;
    g.clearRect(0, 0, W, H);
    const dt = Math.min(0.05, (ts - live.last) / 1000 || 0.016); live.last = ts;
    const playing = store.isPlaying;
    const energy = playing ? Math.min(1, (bands[0] + bands[1] + bands[2] + bands[3] + bands[4]) / 2.6) : 0;
    live.phase += dt * (0.35 + energy * 5);

    // pulse of light on every beat
    if (live.beat > 0.02) {
        const rg = g.createRadialGradient(W / 2, mid, 0, W / 2, mid, W * 0.5);
        rg.addColorStop(0, `rgba(${TC.rgb_teal},${(live.beat * 0.22).toFixed(3)})`); rg.addColorStop(1, `rgba(${TC.rgb_teal},0)`);
        g.fillStyle = rg; g.fillRect(0, 0, W, H);
    }

    // spectrum bars along the bottom
    const sr = store.ctx.sampleRate, n = live.peaks.length, bw = W / n;
    for (let b = 0; b < n; b++) {
        const f = 40 * Math.pow(16000 / 40, b / (n - 1)), bin = clamp(Math.round((f / (sr / 2)) * (spec.length - 1)), 0, spec.length - 1);
        const v = playing ? Math.pow(spec[bin] / 255, 1.4) : 0;
        live.peaks[b] = Math.max(v, live.peaks[b] - 0.012);
        const bh = Math.max(2 * dpr, v * H * 0.34), x = b * bw + bw * 0.18, bwid = bw * 0.64;
        const grad = g.createLinearGradient(0, H, 0, H - H * 0.34);
        grad.addColorStop(0, `rgba(${TC.rgb_teal},0.55)`); grad.addColorStop(1, `rgba(${TC.rgb_amber},0.75)`);
        g.fillStyle = grad;
        g.beginPath(); if (g.roundRect) g.roundRect(x, H - bh, bwid, bh, bwid / 2); else g.rect(x, H - bh, bwid, bh); g.fill();
        if (live.peaks[b] > 0.02) { g.fillStyle = 'rgba(236,239,244,0.7)'; g.fillRect(x, H - live.peaks[b] * H * 0.34 - 4 * dpr, bwid, 2 * dpr); }
    }

    // flowing ribbons
    g.globalCompositeOperation = 'lighter'; g.lineJoin = 'round';
    RIBBONS.forEach((r, i) => {
        const level = playing ? bands[r.band] : 0.03;
        const A = (mid * r.amp) * (0.06 + level * 1.7 + live.beat * 0.3);
        const path = new Path2D();
        for (let x = 0; x <= W; x += 4 * dpr) {
            const u = x / W, env = Math.pow(Math.sin(Math.PI * u), 1.3);
            const y = mid + env * A * (Math.sin(u * Math.PI * 2 * r.freq + live.phase * r.speed + i) + 0.5 * Math.sin(u * Math.PI * 2 * r.freq * 2.1 - live.phase * r.speed * 0.7));
            x === 0 ? path.moveTo(x, y) : path.lineTo(x, y);
        }
        const rgbS = TC['rgb_' + r.c]; g.strokeStyle = `rgba(${rgbS},0.16)`; g.lineWidth = 9 * dpr; g.stroke(path);
        g.strokeStyle = `rgba(${rgbS},0.9)`; g.lineWidth = 2.2 * dpr; g.stroke(path);
    });

    // the actual audio signal, right now
    if (playing) {
        const wave = store.getWave(), len = wave.length, path = new Path2D(), amp = H * 0.3;
        for (let i = 0; i < len; i += 2) {
            const x = (i / len) * W, u = x / W, env = Math.pow(Math.sin(Math.PI * u), 0.6);
            const y = mid + ((wave[i] - 128) / 128) * amp * env;
            i === 0 ? path.moveTo(x, y) : path.lineTo(x, y);
        }
        g.strokeStyle = 'rgba(255,255,255,0.85)'; g.lineWidth = 1.4 * dpr; g.stroke(path);
    }
    g.globalCompositeOperation = 'source-over';
}

function tick() {
    if (store.isPlaying && D() > 0) {
        const t = store.getCurrentTime();
        if (span() < D() * 0.999 && (t < view.start || t > view.end)) setView(t - span() * 0.1, t - span() * 0.1 + span());
        setProgress(t); updateTimeDisplay(t);
    }
    updateMeters();
    const spec = updateAmbient();
    if (waveStyle === 'live' && store.audioBuffer) drawLive(performance.now(), spec);
    if (activeTab === 'eq') drawEQ();
    requestAnimationFrame(tick);
}

$('play-pause-btn').addEventListener('click', togglePlayPause);
stopBtn.addEventListener('click', () => resetPlayState());
startBtn.addEventListener('click', () => seekTo(0));
loopBtn.addEventListener('click', () => loopBtn.classList.toggle('active', store.toggleLoop()));
volumeSlider.addEventListener('input', (e) => { store.setVolume(parseFloat(e.target.value)); setSliderFill(volumeSlider); });
setSliderFill(volumeSlider);

// ---- Mixer faders ----
function makeFader(el, valueEl, initial, onChange) {
    const thumb = el.querySelector('.fader-thumb'), fill = el.querySelector('.fader-fill'), THUMB = 18;
    let value = initial;
    const render = () => {
        thumb.style.bottom = `calc((100% - ${THUMB}px) * ${value})`;
        fill.style.height = `calc((100% - ${THUMB}px) * ${value})`;
        el.setAttribute('aria-valuenow', Math.round(value * 100)); valueEl.textContent = Math.round(value * 100);
    };
    const set = (v) => { value = clamp(v, 0, 1); render(); onChange(value); };
    const fromPointer = (e) => { const r = el.getBoundingClientRect(); set(1 - (e.clientY - r.top - THUMB / 2) / (r.height - THUMB)); };
    el.addEventListener('pointerdown', (e) => { el.setPointerCapture(e.pointerId); fromPointer(e); });
    el.addEventListener('pointermove', (e) => { if (el.hasPointerCapture(e.pointerId)) fromPointer(e); });
    el.addEventListener('dblclick', () => set(initial));
    el.addEventListener('keydown', (e) => {
        if (e.key === 'ArrowUp' || e.key === 'ArrowRight') { e.preventDefault(); set(value + 0.02); }
        if (e.key === 'ArrowDown' || e.key === 'ArrowLeft') { e.preventDefault(); set(value - 0.02); }
    });
    set(initial);
}
makeFader($('master-fader'), $('master-value'), 0.8, (v) => store.setMasterVolume(v));
makeFader($('voice-fader'), $('voice-value'), 0.9, (v) => store.setVoiceVolume(v));

// =====================================================================
// Equalizer (live, draggable)
// =====================================================================
const eqCanvas = $('eq-canvas');
const EQ = { FMIN: 20, FMAX: 20000, GR: 12, ranges: { low: [30, 400], mid: [200, 6000], high: [2000, 16000] }, names: { low: 'Low', mid: 'Mid', high: 'High' } };
let eqHover = null, eqDrag = null;
const eqX = (f, w) => (Math.log(f / EQ.FMIN) / Math.log(EQ.FMAX / EQ.FMIN)) * w;
const eqF = (x, w) => EQ.FMIN * Math.pow(EQ.FMAX / EQ.FMIN, x / w);
const eqY = (g, h) => h / 2 - (g / EQ.GR) * (h / 2 - 16);
const eqG = (y, h) => ((h / 2 - y) / (h / 2 - 16)) * EQ.GR;
const fmtHz = (f) => f >= 1000 ? (f / 1000).toFixed(f >= 10000 ? 0 : 1) + ' kHz' : Math.round(f) + ' Hz';
const eqFreqs = (() => { const a = new Float32Array(140); for (let i = 0; i < a.length; i++) a[i] = EQ.FMIN * Math.pow(EQ.FMAX / EQ.FMIN, i / (a.length - 1)); return a; })();

function eqReadout(band) {
    const p = store.getEQ()[band];
    $('eq-readout').textContent = `${EQ.names[band]} \u00b7 ${fmtHz(p.freq)} \u00b7 ${p.gain > 0 ? '+' : ''}${p.gain.toFixed(1)} dB` + (band === 'mid' ? ` \u00b7 Q ${p.q.toFixed(1)}` : '');
}
function drawEQ() {
    const dpr = window.devicePixelRatio || 1, w = eqCanvas.clientWidth, h = eqCanvas.clientHeight;
    if (w <= 0) return;
    sizeCanvas(eqCanvas, w, h, dpr);
    const g = eqCanvas.getContext('2d');
    g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);

    // grid
    g.lineWidth = 1; g.font = '500 9px "JetBrains Mono", monospace'; g.textBaseline = 'alphabetic';
    [100, 1000, 10000].forEach(f => { const x = Math.round(eqX(f, w)) + 0.5; g.strokeStyle = '#242a35'; g.beginPath(); g.moveTo(x, 0); g.lineTo(x, h); g.stroke(); g.fillStyle = '#566072'; const near = x + 44 > w; g.textAlign = near ? 'right' : 'left'; g.fillText(fmtHz(f), near ? x - 4 : x + 4, h - 5); g.textAlign = 'left'; });
    [-6, 0, 6].forEach(db => { const y = Math.round(eqY(db, h)) + 0.5; g.strokeStyle = db === 0 ? '#323a48' : '#1f242d'; g.beginPath(); g.moveTo(0, y); g.lineTo(w, y); g.stroke(); g.fillStyle = '#566072'; g.fillText((db > 0 ? '+' : '') + db, 4, y - 3); });

    // live spectrum behind the curve
    const spec = store.getSpectrum(), sr = store.ctx.sampleRate, bins = spec.length;
    const sg = g.createLinearGradient(0, h, 0, 0); sg.addColorStop(0, `rgba(${TC.rgb_teal},0)`); sg.addColorStop(1, `rgba(${TC.rgb_teal},0.42)`);
    g.beginPath(); g.moveTo(0, h);
    for (let x = 0; x <= w; x += 2) {
        const bin = clamp(Math.round((eqF(x, w) / (sr / 2)) * (bins - 1)), 0, bins - 1);
        g.lineTo(x, h - (spec[bin] / 255) * h * 0.85);
    }
    g.lineTo(w, h); g.closePath(); g.fillStyle = sg; g.fill();

    // response curve
    const resp = store.eqResponse(eqFreqs);
    g.beginPath();
    for (let i = 0; i < eqFreqs.length; i++) { const x = eqX(eqFreqs[i], w), y = eqY(clamp(resp[i], -EQ.GR, EQ.GR), h); i ? g.lineTo(x, y) : g.moveTo(x, y); }
    g.strokeStyle = TC.amber; g.lineWidth = 2.5; g.shadowColor = `rgba(${TC.rgb_amber},0.7)`; g.shadowBlur = 10; g.stroke(); g.shadowBlur = 0;
    g.lineTo(w, eqY(0, h)); g.lineTo(0, eqY(0, h)); g.closePath(); g.fillStyle = `rgba(${TC.rgb_amber},0.10)`; g.fill();

    // nodes
    const p = store.getEQ();
    for (const band of ['low', 'mid', 'high']) {
        const x = eqX(p[band].freq, w), y = eqY(p[band].gain, h), active = eqDrag === band || eqHover === band;
        g.beginPath(); g.arc(x, y, active ? 9 : 7, 0, Math.PI * 2);
        g.fillStyle = active ? '#ffffff' : TC.amberLight; g.shadowColor = `rgba(${TC.rgb_amber},0.8)`; g.shadowBlur = active ? 14 : 6; g.fill(); g.shadowBlur = 0;
        g.lineWidth = 2; g.strokeStyle = '#14171c'; g.stroke();
        g.fillStyle = '#9aa3b2'; g.textAlign = 'center'; g.fillText(EQ.names[band], x, y < 22 ? y + 22 : y - 14); g.textAlign = 'start';
    }
}
function eqPointer(e) { const r = eqCanvas.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top, w: r.width, h: r.height }; }
function eqHit(pt) {
    const p = store.getEQ(); let best = null, bd = 18;
    for (const band of ['low', 'mid', 'high']) { const d = Math.hypot(eqX(p[band].freq, pt.w) - pt.x, eqY(p[band].gain, pt.h) - pt.y); if (d < bd) { bd = d; best = band; } }
    return best;
}
eqCanvas.addEventListener('pointerdown', (e) => {
    const pt = eqPointer(e), band = eqHit(pt); if (!band) return;
    eqDrag = band; eqCanvas.setPointerCapture(e.pointerId); eqReadout(band);
});
eqCanvas.addEventListener('pointermove', (e) => {
    const pt = eqPointer(e);
    if (eqDrag) {
        const [lo, hi] = EQ.ranges[eqDrag];
        store.setEQ(eqDrag, { freq: clamp(eqF(clamp(pt.x, 0, pt.w), pt.w), lo, hi), gain: clamp(Math.round(eqG(pt.y, pt.h) * 10) / 10, -EQ.GR, EQ.GR) });
        eqReadout(eqDrag);
    } else { eqHover = eqHit(pt); eqCanvas.style.cursor = eqHover ? 'grab' : 'default'; }
});
eqCanvas.addEventListener('pointerup', () => { eqDrag = null; });
eqCanvas.addEventListener('dblclick', (e) => { const b = eqHit(eqPointer(e)); if (b) { store.setEQ(b, { gain: 0 }); eqReadout(b); } });
eqCanvas.addEventListener('wheel', (e) => {
    const b = eqHit(eqPointer(e)) || eqHover;
    if (b !== 'mid') return;
    e.preventDefault();
    store.setEQ('mid', { q: clamp(store.getEQ().mid.q * Math.exp(-e.deltaY * 0.003), 0.3, 8) }); eqReadout('mid');
}, { passive: false });
$('eq-flat').addEventListener('click', () => { store.resetEQ(); $('eq-readout').textContent = 'Flat'; });
$('eq-apply').addEventListener('click', () => {
    if (store.eqIsFlat()) return toast('The EQ is flat. Move a point first.', 'error');
    const r = currentRegion();
    withBusy('Applying EQ...', () => commit('EQ applied to audio' + (r ? ' (selection)' : ''), async () => {
        await store.processRegion(r ? r.a : null, r ? r.b : null, (b) => store.bakeEQ(b), { keepLength: !!r });
        store.resetEQ(); $('eq-readout').textContent = 'Flat';
    }, { keepMarkers: true }));
});

// =====================================================================
// Analyze: loudness and silences
// =====================================================================
const TARGET_NAMES = { '-16': 'podcasts', '-14': 'streaming', '-23': 'radio' };
let lastLoudness = null;
function markAnalysisDirty() {
    analysisDirty = true;
    if (activeTab === 'analyze') { clearTimeout(markAnalysisDirty.t); markAnalysisDirty.t = setTimeout(runAnalysis, 200); }
}
function runAnalysis() {
    analysisDirty = false;
    if (!store.audioBuffer) return;
    lastLoudness = store.measureLoudness(store.audioBuffer);
    updateLoudnessUI(); updateSilences();
}
function updateLoudnessUI() {
    const m = lastLoudness, ok = m && isFinite(m.lufs);
    $('lufs-num').textContent = ok ? m.lufs.toFixed(1) : '--';
    $('peak-chip').textContent = m && isFinite(m.peakDb) ? `Peak ${m.peakDb.toFixed(1)} dB` : 'Peak --';
    $('peak-chip').classList.toggle('hot', !!m && m.peakDb > -0.1);
    const pct = (v) => clamp((v + 36) / 30, 0, 1) * 100;
    $('gauge-target').style.left = pct(loudTarget - 1) + '%';
    $('gauge-target').style.width = (pct(loudTarget + 1) - pct(loudTarget - 1)) + '%';
    $('gauge-marker').style.left = ok ? pct(m.lufs) + '%' : '0%';
    const v = $('verdict');
    if (!ok) { v.textContent = store.audioBuffer ? 'Too quiet to measure.' : 'Import audio to measure it.'; v.classList.remove('good'); return; }
    const diff = m.lufs - loudTarget, name = TARGET_NAMES[loudTarget];
    if (Math.abs(diff) <= 1) { v.textContent = `On target for ${name}.`; v.classList.add('good'); }
    else { v.textContent = `${Math.abs(diff).toFixed(1)} LU too ${diff < 0 ? 'quiet' : 'loud'} for ${name}.`; v.classList.remove('good'); }
}
document.querySelectorAll('#target-seg .seg').forEach(b => b.addEventListener('click', () => {
    document.querySelectorAll('#target-seg .seg').forEach(x => x.classList.toggle('active', x === b));
    loudTarget = parseInt(b.dataset.target, 10); updateLoudnessUI();
}));
$('match-btn').addEventListener('click', () => {
    if (!lastLoudness || !isFinite(lastLoudness.lufs)) return toast('Nothing to match yet.', 'error');
    commit(`Matched to ${loudTarget} LUFS`, () => store.processRegion(null, null, (b) => store.matchLoudness(b, loudTarget)), { keepMarkers: true });
});

const silInputs = { thr: $('sil-thr'), min: $('sil-min'), keep: $('sil-keep') };
function updateSilences() {
    if (!store.audioBuffer) { silences = []; renderSilences(); return; }
    const thr = +silInputs.thr.value, min = +silInputs.min.value, keep = +silInputs.keep.value;
    silences = store.detectSilences(store.audioBuffer, thr, min);
    const total = silences.reduce((a, [s, e]) => a + (e - s), 0), saved = silences.reduce((a, [s, e]) => a + Math.max(0, (e - s) - keep / 1000), 0);
    $('sil-summary').textContent = silences.length
        ? `Found ${silences.length} silence${silences.length > 1 ? 's' : ''} (${total.toFixed(1)}s). Removing them saves ${saved.toFixed(1)}s.`
        : 'No silences found at these settings.';
    renderSilences();
}
let silTimer;
Object.entries({ thr: ' dB', min: ' ms', keep: ' ms' }).forEach(([k, unit]) => {
    const input = silInputs[k], out = $(`sil-${k === 'thr' ? 'thr' : k}-out`);
    setSliderFill(input);
    input.addEventListener('input', () => { out.textContent = input.value + unit; setSliderFill(input); clearTimeout(silTimer); silTimer = setTimeout(updateSilences, 60); });
});
$('sil-apply').addEventListener('click', () => {
    updateSilences();
    if (!silences.length) return toast('No silences to remove at these settings.', 'error');
    const keep = +silInputs.keep.value, saved = silences.reduce((a, [s, e]) => a + Math.max(0, (e - s) - keep / 1000), 0);
    commit(`Removed ${saved.toFixed(1)}s of silence`, () => store.removeSilences(silences, keep));
});

// =====================================================================
// Tabs
// =====================================================================
function setTab(name) {
    activeTab = name;
    document.querySelectorAll('.tab').forEach(t => t.classList.toggle('active', t.dataset.tab === name));
    document.querySelectorAll('.tab-pane').forEach(p => { p.hidden = p.id !== `pane-${name}`; });
    if (name === 'eq') drawEQ();
    if (name === 'analyze' && analysisDirty) runAnalysis();
    renderSilences();
    if (typeof onTabChanged === 'function') onTabChanged(name);
}
document.querySelectorAll('.tab').forEach(t => t.addEventListener('click', () => setTab(t.dataset.tab)));

// =====================================================================
// Editing: one commit path for every change (undo, redraw, markers)
// =====================================================================
function currentRegion() { return sel && sel.b - sel.a >= 0.05 ? sel : null; }

async function commit(label, mutate, opts = {}) {
    if (typeof masterGuard === 'function') masterGuard(); // leave the Master preview before editing
    if (!store.audioBuffer) { toast('Import audio first.', 'error'); return; }
    const wasPlaying = store.isPlaying;
    if (wasPlaying) store.pause();
    const prevLen = store.audioBuffer.length;
    store.snapshot(label ? label.replace(/ \(selection\)$/, '') : 'Edit', { markers: markers.map(m => ({ ...m })), assets: assets.map(a => ({ ...a })), subs: typeof subsSnapshot === 'function' ? subsSnapshot() : null });
    try { await mutate(); }
    catch (err) {
        console.error(err); store.history.pop();
        toast("That didn't work. Try a different selection or file.", 'error');
        if (wasPlaying) store.play();
        return;
    }
    const same = store.audioBuffer.length === prevLen;
    if (!same) {
        if (opts.mapTime) markers = markers.map(m => { const t = opts.mapTime(m.t); return t == null ? null : { ...m, t }; }).filter(Boolean);
        else if (!opts.keepMarkers) markers = [];
        markers = markers.filter(m => m.t >= 0 && m.t <= D());
        silences = [];
        if (typeof mapSubs === 'function') mapSubs(opts); // lyrics follow cuts, pastes and tempo changes
    }
    bufferChanged(same);
    refreshUndo();
    setProgress(store.pauseOffset); updateTimeDisplay(store.pauseOffset);
    if (wasPlaying) store.play();
    if (label) toast(label, 'ok', { action: { label: 'Undo', run: actions.undo } });
}

// Effects work on the selection when there is one, otherwise on the whole track.
function effect(label, fn, { busy = false, resize = null } = {}) {
    return () => {
        if (!store.audioBuffer) return toast('Import audio first.', 'error');
        const r = currentRegion(), suffix = r ? ' (selection)' : '';
        const run = () => commit(label + suffix,
            () => store.processRegion(r ? r.a : null, r ? r.b : null, fn, { keepLength: !!r && !resize }),
            { keepMarkers: !resize, mapTime: resize && !r ? (t) => t / resize : undefined, tempo: !!resize });
        return busy ? withBusy(label.replace(/ (applied|added)$/, '') + '...', run) : run();
    };
}

const markerMeta = () => ({ markers: markers.map(m => ({ ...m })), assets: assets.map(a => ({ ...a })), subs: typeof subsSnapshot === 'function' ? subsSnapshot() : null });
function restoreAfterTravel(prevLen, message, withRedo = false) {
    const m = store.restoredMeta;
    if (m && m.assets) { assets = m.assets.map(x => ({ ...x })); renderAssets(); }
    if (m && m.subs && typeof subsRestore === 'function') subsRestore(m.subs);
    if (m && m.markers) markers = m.markers.map(x => ({ ...x }));
    else if (store.audioBuffer.length !== prevLen) markers = [];
    silences = [];
    resetPlayState(); clearSelection(); bufferChanged(false); refreshUndo();
    toast(message, 'ok', withRedo && store.canRedo() ? { action: { label: 'Redo', icon: 'redo', run: actions.redo } } : {});
}

const actions = {
    cut() {
        const r = sel; if (!r || r.b - r.a < 0.1) return toast('Select a region on the waveform to cut.', 'error');
        const { a, b } = r, len = b - a; clearSelection();
        commit('Region cut', () => store.cut(a, b), { mapTime: (t) => (t > a && t < b) ? null : (t >= b ? t - len : t) });
    },
    trim() {
        const r = sel; if (!r || r.b - r.a < 0.1) return toast('Select a region on the waveform to keep.', 'error');
        const { a, b } = r; clearSelection();
        commit('Trimmed to selection', () => store.trim(a, b), { mapTime: (t) => (t >= a && t <= b) ? t - a : null });
    },
    marker() {
        if (!store.audioBuffer) return toast('Import audio first.', 'error');
        const t = store.getCurrentTime();
        const mk = { t, name: '' };
        markers.push(mk); markers.sort((x, y) => x.t - y.t); renderMarkers();
        toast(`Marker ${markers.indexOf(mk) + 1} at ${fmtTime(t)}. Double-click it to name it.`);
    },
    jumpMarker(dir) {
        if (!markers.length) return toast('No markers yet. Press M to add one.', 'error');
        const t = store.getCurrentTime();
        const hit = dir > 0 ? markers.find(m => m.t > t + 0.05) : [...markers].reverse().find(m => m.t < t - 0.05), target = hit ? hit.t : undefined;
        if (target === undefined) return toast(dir > 0 ? 'No later markers.' : 'No earlier markers.', 'error');
        seekTo(target);
    },
    undo() {
        if (typeof masterGuard === 'function') masterGuard();
        if (!store.canUndo()) return toast('Nothing to undo.', 'error');
        const prevLen = store.audioBuffer.length;
        if (store.undo(markerMeta())) restoreAfterTravel(prevLen, 'Undid last edit', true);
    },
    redo() {
        if (typeof masterGuard === 'function') masterGuard();
        if (!store.canRedo()) return toast('Nothing to redo.', 'error');
        const prevLen = store.audioBuffer.length;
        if (store.redo(markerMeta())) restoreAfterTravel(prevLen, 'Redid edit', true);
    },
    async reset() {
        if (!store.audioBuffer) return;
        const ok = await openModal({ title: 'Reset to original?', message: 'This removes every cut, trim, fade and effect, and restores the file you first imported.', confirmLabel: 'Reset audio', danger: true });
        if (!ok) return;
        const buffer = store.resetToOriginal();
        if (buffer) {
            markers = []; silences = []; store.resetEQ();
            resetPlayState(); clearSelection(); assets = assets.slice(0, 1); renderAssets();
            bufferChanged(false); refreshUndo(); toast('Restored original audio');
        }
    },
    filter() {
        const on = store.toggleEffect(); $('effects-btn').classList.toggle('active', on);
        toast(on ? 'Studio filter on' : 'Studio filter off');
    },
    export() {
        if (!store.audioBuffer) return toast('Nothing to export yet. Import a file first.', 'error');
        const blob = store.exportWAV(); if (!blob) return;
        const url = URL.createObjectURL(blob), a = document.createElement('a');
        a.style.display = 'none'; a.href = url; a.download = `${$('project-name-text').innerText}_Export.wav`;
        document.body.appendChild(a); a.click();
        setTimeout(() => { document.body.removeChild(a); URL.revokeObjectURL(url); }, 100);
        toast('Exported WAV');
    },
    selectAll() { if (!store.audioBuffer) return; sel = { a: 0, b: D() }; renderSelection(); }
};

$('cut-btn').addEventListener('click', actions.cut);
$('trim-btn').addEventListener('click', actions.trim);
$('marker-btn').addEventListener('click', actions.marker);
$('reset-btn').addEventListener('click', actions.reset);
$('effects-btn').addEventListener('click', actions.filter);
undoBtn.addEventListener('click', actions.undo);
$('nav-redo').addEventListener('click', actions.redo);
$('hist-undo').addEventListener('click', actions.undo);
$('hist-redo').addEventListener('click', actions.redo);

const fxList = {
    robo: effect('Robo-tune applied', (b) => store.fxRobo(b)),
    fadeIn: effect('Fade in applied', (b) => store.fxFadeIn(b, currentRegion() ? b.duration : 3)),
    fadeOut: effect('Fade out applied', (b) => store.fxFadeOut(b, currentRegion() ? b.duration : 3)),
    normalize: effect('Normalized to full scale', (b) => store.fxNormalize(b)),
    reverse: effect('Audio reversed', (b) => store.fxReverse(b)),
    polish: effect('Podcast polish applied', (b) => store.polish(b), { busy: true }),
    room: effect('Room reverb added', (b) => store.reverb(b, { sec: 0.9, decay: 4, wet: 0.25, tail: 0.9 }), { busy: true }),
    hall: effect('Hall reverb added', (b) => store.reverb(b, { sec: 2.8, decay: 3, wet: 0.35, tail: 2.8 }), { busy: true }),
    echo: effect('Echo added', (b) => store.echo(b), { busy: true }),
    phone: effect('Telephone effect applied', (b) => store.telephone(b), { busy: true }),
    deep: effect('Deep voice applied', (b) => store.fxResample(b, 0.8), { resize: 0.8 }),
    chip: effect('Chipmunk voice applied', (b) => store.fxResample(b, 1.35), { resize: 1.35 })
};
$('autotune-btn').addEventListener('click', fxList.robo);
$('fade-in-btn').addEventListener('click', fxList.fadeIn);
$('fade-out-btn').addEventListener('click', fxList.fadeOut);
$('normalize-btn').addEventListener('click', fxList.normalize);
$('reverse-btn').addEventListener('click', fxList.reverse);
$('polish-btn').addEventListener('click', () => fxList.polish());
$('lab-room').addEventListener('click', fxList.room);
$('lab-hall').addEventListener('click', fxList.hall);
$('lab-echo').addEventListener('click', fxList.echo);
$('lab-phone').addEventListener('click', fxList.phone);
$('lab-deep').addEventListener('click', fxList.deep);
$('lab-chip').addEventListener('click', fxList.chip);

// =====================================================================
// Loading files, drag and drop, append
// =====================================================================
async function loadFile(file) {
    if (!file) return;
    if (typeof masterGuard === 'function') masterGuard();
    try {
        const buffer = await store.loadAudio(await file.arrayBuffer());
        resetPlayState(); sel = null; markers = []; silences = []; store.resetEQ();
        assets = [{ name: file.name, appended: false }]; renderAssets();
        setHasAudio(true);
        container.classList.remove('reveal'); void container.offsetWidth; container.classList.add('reveal');
        bufferChanged(false);
        if (typeof onFileLoaded === 'function') onFileLoaded(file);
        toast(`Loaded ${file.name}`);
    } catch (err) {
        console.error(err);
        toast("Couldn't read that file. Try an MP3, WAV, M4A or OGG.", 'error');
    }
}
fileInput.addEventListener('change', async (e) => { await loadFile(e.target.files[0]); fileInput.value = ''; });
$('upload-trigger').addEventListener('click', () => fileInput.click());
$('empty-import-btn').addEventListener('click', () => fileInput.click());

const dropZone = $('drop-zone');
['dragenter', 'dragover'].forEach(t => dropZone.addEventListener(t, (e) => { e.preventDefault(); dropZone.classList.add('drag-over'); }));
['dragleave', 'drop'].forEach(t => dropZone.addEventListener(t, (e) => { e.preventDefault(); if (t === 'drop' || e.target === dropZone) dropZone.classList.remove('drag-over'); }));
dropZone.addEventListener('drop', (e) => {
    const file = e.dataTransfer.files[0];
    if (file && file.type.startsWith('audio/')) loadFile(file); else if (file) toast('That file is not audio.', 'error');
});

$('merge-btn').addEventListener('click', () => {
    if (!store.audioBuffer) return toast('Import a main audio file first.', 'error');
    mergeInput.click();
});
mergeInput.addEventListener('change', async (e) => {
    const file = e.target.files[0]; if (!file) return;
    try {
        if (store.ctx.state === 'suspended') await Promise.race([store.ctx.resume(), new Promise((r) => setTimeout(r, 600))]);
        const nb = await store.ctx.decodeAudioData(await file.arrayBuffer());
        if (typeof appendWithDialog === 'function') await appendWithDialog(file, nb);
        else { await commit(`Appended ${file.name}`, () => store.appendAudio(nb), { keepMarkers: true }); assets.push({ name: file.name, appended: true }); renderAssets(); clearSelection(); }
    } catch (err) { console.error(err); toast("Couldn't append that file.", 'error'); }
    mergeInput.value = '';
});

// =====================================================================
// Waveform style, top bar
// =====================================================================
function setWaveStyle(style) {
    if (waveStyle === 'live' && style !== 'live') liveCanvas.getContext('2d').clearRect(0, 0, liveCanvas.width, liveCanvas.height);
    waveStyle = style;
    $('view-bars').classList.toggle('active', style === 'bars');
    $('view-smooth').classList.toggle('active', style === 'smooth');
    $('view-live').classList.toggle('active', style === 'live');
    $('view-spectro').classList.toggle('active', style === 'spectro');
    scheduleDraw();
}
$('view-bars').addEventListener('click', () => setWaveStyle('bars'));
$('view-smooth').addEventListener('click', () => setWaveStyle('smooth'));
$('view-live').addEventListener('click', () => setWaveStyle('live'));
$('view-spectro').addEventListener('click', () => setWaveStyle('spectro'));

$('nav-profile').addEventListener('click', () => toast('Signed in as Arsh Mhatre'));
$('nav-profile').addEventListener('keydown', (e) => { if (e.key === 'Enter') toast('Signed in as Arsh Mhatre'); });
$('project-title-btn').addEventListener('click', async () => {
    const name = await openModal({ title: 'Rename project', input: $('project-name-text').innerText, confirmLabel: 'Save name' });
    if (name && name.trim()) $('project-name-text').innerText = name.trim();
});

// =====================================================================
// Command palette
// =====================================================================
const palette = $('palette'), palInput = $('palette-input'), palList = $('palette-list');
const commandList = () => [...(typeof extraCommands === 'function' ? extraCommands() : []),
{ name: 'Play or pause', icon: 'play_arrow', hint: 'Space', run: togglePlayPause },
{ name: 'Podcast polish', icon: 'auto_awesome', hint: 'One click', run: fxList.polish },
{ name: 'Remove silences', icon: 'volume_off', hint: 'Analyze', run: () => { setTab('analyze'); } },
{ name: 'Match loudness to target', icon: 'speed', hint: 'Analyze', run: () => { setTab('analyze'); $('match-btn').click(); } },
{ name: 'Cut selected region', icon: 'content_cut', hint: 'Del', run: actions.cut },
{ name: 'Trim to selection', icon: 'crop', hint: '', run: actions.trim },
{ name: 'Select phrase at playhead', icon: 'text_select_move_forward_word', hint: 'Dbl-click', run: () => selectPhraseAt(store.getCurrentTime()) },
{ name: 'Select all', icon: 'select_all', hint: isMac ? '\u2318A' : 'Ctrl A', run: actions.selectAll },
{ name: 'Add marker at playhead', icon: 'flag', hint: 'M', run: actions.marker },
{ name: 'Jump to next marker', icon: 'skip_next', hint: '.', run: () => actions.jumpMarker(1) },
{ name: 'Jump to previous marker', icon: 'skip_previous', hint: ',', run: () => actions.jumpMarker(-1) },
{ name: 'Redo', icon: 'redo', hint: isMac ? '\u2318\u21e7Z' : 'Ctrl Shift Z', run: actions.redo },
{ name: 'Show history', icon: 'history', hint: 'Panel', run: () => setTab('history') },
{ name: 'Undo', icon: 'undo', hint: isMac ? '\u2318Z' : 'Ctrl Z', run: actions.undo },
{ name: 'Fade in', icon: 'trending_up', hint: '', run: fxList.fadeIn },
{ name: 'Fade out', icon: 'trending_down', hint: '', run: fxList.fadeOut },
{ name: 'Normalize', icon: 'equalizer', hint: '', run: fxList.normalize },
{ name: 'Reverse', icon: 'swap_horiz', hint: '', run: fxList.reverse },
{ name: 'Robo-tune', icon: 'mic_external_on', hint: '', run: fxList.robo },
{ name: 'Room reverb', icon: 'meeting_room', hint: 'Sound lab', run: fxList.room },
{ name: 'Hall reverb', icon: 'stadium', hint: 'Sound lab', run: fxList.hall },
{ name: 'Echo', icon: 'graphic_eq', hint: 'Sound lab', run: fxList.echo },
{ name: 'Telephone voice', icon: 'call', hint: 'Sound lab', run: fxList.phone },
{ name: 'Deep voice', icon: 'arrow_downward', hint: 'Sound lab', run: fxList.deep },
{ name: 'Chipmunk voice', icon: 'arrow_upward', hint: 'Sound lab', run: fxList.chip },
{ name: 'Toggle studio filter', icon: 'blur_on', hint: '', run: actions.filter },
{ name: 'Show waveform as bars', icon: 'align_vertical_center', hint: 'View', run: () => setWaveStyle('bars') },
{ name: 'Show waveform as smooth shape', icon: 'show_chart', hint: 'View', run: () => setWaveStyle('smooth') },
{ name: 'Show live moving waves', icon: 'waves', hint: 'View', run: () => setWaveStyle('live') },
{ name: 'Show spectrogram', icon: 'blur_linear', hint: 'View', run: () => setWaveStyle('spectro') },
{ name: 'Zoom to fit', icon: 'fit_screen', hint: '0', run: fitView },
{ name: 'Open mixer', icon: 'tune', hint: 'Panel', run: () => setTab('mixer') },
{ name: 'Open equalizer', icon: 'graphic_eq', hint: 'Panel', run: () => setTab('eq') },
{ name: 'Open analyzer', icon: 'monitoring', hint: 'Panel', run: () => setTab('analyze') },
{ name: 'Import audio', icon: 'folder_open', hint: '', run: () => fileInput.click() },
{ name: 'Export WAV', icon: 'download', hint: '', run: actions.export },
{ name: 'Reset to original', icon: 'restore', hint: '', run: actions.reset }
];
let palItems = [], palSel = 0;
function renderPalette() {
    const q = palInput.value.trim().toLowerCase();
    palItems = commandList().filter(c => !q || c.name.toLowerCase().includes(q) || c.hint.toLowerCase().includes(q));
    palSel = Math.min(palSel, Math.max(0, palItems.length - 1));
    palList.innerHTML = '';
    if (!palItems.length) { palList.innerHTML = '<li class="pal-empty">No matching action.</li>'; return; }
    palItems.forEach((c, i) => {
        const li = document.createElement('li');
        li.className = 'pal-item' + (i === palSel ? ' sel' : '');
        li.innerHTML = `<span class="material-symbols-rounded">${c.icon}</span><span class="pal-name"></span>${c.hint ? '<kbd></kbd>' : ''}`;
        li.querySelector('.pal-name').textContent = c.name;
        if (c.hint) li.querySelector('kbd').textContent = c.hint;
        li.addEventListener('mousemove', () => { if (palSel !== i) { palSel = i; renderPalette(); } });
        li.addEventListener('click', () => runPalette(i));
        palList.appendChild(li);
    });
    const s = palList.querySelector('.sel'); if (s) s.scrollIntoView({ block: 'nearest' });
}
function openPalette() { palette.hidden = false; palInput.value = ''; palSel = 0; renderPalette(); palInput.focus(); }
function closePalette() { palette.hidden = true; palInput.blur(); }
function runPalette(i) { const c = palItems[i]; closePalette(); if (c) setTimeout(c.run, 0); }
palInput.addEventListener('input', () => { palSel = 0; renderPalette(); });
palInput.addEventListener('keydown', (e) => {
    if (e.key === 'ArrowDown') { e.preventDefault(); palSel = Math.min(palItems.length - 1, palSel + 1); renderPalette(); }
    else if (e.key === 'ArrowUp') { e.preventDefault(); palSel = Math.max(0, palSel - 1); renderPalette(); }
    else if (e.key === 'Enter') { e.preventDefault(); runPalette(palSel); }
    else if (e.key === 'Escape') { e.preventDefault(); closePalette(); }
});
palette.addEventListener('mousedown', (e) => { if (e.target === palette) closePalette(); });
$('palette-btn').addEventListener('click', openPalette);

// =====================================================================
// Keyboard
// =====================================================================
document.addEventListener('keydown', (e) => {
    const mod = e.metaKey || e.ctrlKey;
    if (mod && e.key.toLowerCase() === 'k') { e.preventDefault(); palette.hidden ? openPalette() : closePalette(); return; }
    const typing = e.target.tagName === 'INPUT' && e.target.type === 'text';
    if (typing || !$('modal').hidden || !palette.hidden || document.querySelector('.modal:not([hidden])')) return;

    if (e.code === 'Space' && !e.target.closest('[role=slider]') && e.target.type !== 'range') { e.preventDefault(); togglePlayPause(); }
    else if (mod && e.key.toLowerCase() === 'z') { e.preventDefault(); e.shiftKey ? actions.redo() : actions.undo(); }
    else if (mod && e.key.toLowerCase() === 'y') { e.preventDefault(); actions.redo(); }
    else if (mod && e.key.toLowerCase() === 'a') { e.preventDefault(); actions.selectAll(); }
    else if ((e.key === 'Delete' || e.key === 'Backspace') && sel) { e.preventDefault(); actions.cut(); }
    else if (e.key === 'Escape') clearSelection();
    else if (mod) return;
    else if (e.key.toLowerCase() === 'm') actions.marker();
    else if (e.key.toLowerCase() === 'l') loopBtn.click();
    else if (e.key === ',') actions.jumpMarker(-1);
    else if (e.key === '.') actions.jumpMarker(1);
    else if (e.key === '+' || e.key === '=') $('zoom-in').click();
    else if (e.key === '-') $('zoom-out').click();
    else if (e.key === '0') fitView();
});

// =====================================================================
// Boot
// =====================================================================
setHasAudio(false);
updateStats(); updateLoudnessUI(); updateZoomLabel();
requestAnimationFrame(tick);

/* =====================================================================
   Chronos Pro - studio features
   Loaded after main.js. Uses its helpers: store, commit, effect, toast, ...
   ===================================================================== */

// ---------- small helpers ----------
const fmtDb = (v) => `${v > 0 ? '+' : ''}${v} dB`;
const FMT = {
    db: fmtDb, dbPlain: (v) => `${v} dB`, ratio: (v) => `${v}:1`, ms: (v) => `${v} ms`, pct: (v) => `${v}%`,
    st: (v) => `${v > 0 ? '+' : ''}${v} st`, sec: (v) => `${v}s`
};
function bindRange(id, fmt, cb) {
    const el = $(id), out = $(id + '-out');
    const update = () => { out.textContent = fmt(+el.value); setSliderFill(el); };
    el.addEventListener('input', () => { update(); if (cb) cb(+el.value); });
    update();
    return el;
}
const val = (id) => +$(id).value;

// ---------- scope notes: "applies to the selection / whole track" ----------
function updateScopeNotes() {
    const r = currentRegion();
    document.querySelectorAll('[data-scope]').forEach((el) => {
        el.textContent = r ? `Applies to your selection (${(r.b - r.a).toFixed(1)}s)` : 'Applies to the whole track';
        el.classList.toggle('is-selection', !!r);
    });
    $('play-pause-btn').title = r ? 'Play the selection (Space). Press Esc to clear it and play everything.' : 'Play / Pause (Space)';
    updateTimeInfo();
}

// =====================================================================
// Mixer: pan and stereo tools
// =====================================================================
$('pan-slider').addEventListener('input', (e) => {
    const v = +e.target.value;
    store.setPan(v);
    $('pan-out').textContent = Math.abs(v) < 0.03 ? 'Center' : `${Math.round(Math.abs(v) * 100)}% ${v < 0 ? 'left' : 'right'}`;
    setSliderFill(e.target);
});
$('pan-slider').addEventListener('dblclick', (e) => { e.target.value = 0; e.target.dispatchEvent(new Event('input')); });
$('pan-slider').style.setProperty('--fill', '50%');

const needsStereo = (fn) => (b) => { if (b.numberOfChannels < 2) throw new Error('mono'); return fn(b); };
function stereoTool(label, fn) {
    return () => {
        if (store.audioBuffer && store.audioBuffer.numberOfChannels < 2) return toast('This track is mono, so there is nothing to change between left and right.', 'error');
        return effect(label, fn)();
    };
}
$('st-mono').addEventListener('click', stereoTool('Converted to mono', (b) => store.fxMono(b)));
$('st-swap').addEventListener('click', stereoTool('Left and right swapped', (b) => store.fxSwap(b)));
$('st-wide').addEventListener('click', stereoTool('Stereo widened', (b) => store.fxMidSide(b, { mid: 1, side: 1.6 })));
$('st-novox').addEventListener('click', stereoTool('Centre vocals removed', (b) => store.fxRemoveVocals(b)));
$('st-vox').addEventListener('click', stereoTool('Centre vocals isolated', (b) => store.fxIsolateVocals(b)));

// =====================================================================
// Dynamics: live compressor, limiter, gain
// =====================================================================
const compOn = $('comp-on');
compOn.addEventListener('change', () => store.setComp({ enabled: compOn.checked }));
bindRange('comp-thr', FMT.dbPlain, (v) => store.setComp({ threshold: v }));
bindRange('comp-ratio', FMT.ratio, (v) => store.setComp({ ratio: v }));
bindRange('comp-atk', FMT.ms, (v) => store.setComp({ attack: v }));
bindRange('comp-rel', FMT.ms, (v) => store.setComp({ release: v }));
bindRange('comp-mk', FMT.db, (v) => store.setComp({ makeup: v }));
bindRange('lim-ceil', FMT.dbPlain);
bindRange('gain-db', FMT.db);

$('comp-bake').addEventListener('click', async () => {
    if (!store.audioBuffer) return;
    const r = currentRegion();
    await withBusy('Applying compressor...', () => commit('Compressor applied' + (r ? ' (selection)' : ''), async () => {
        await store.processRegion(r ? r.a : null, r ? r.b : null, (b) => store.bakeCompressor(b), { keepLength: !!r });
    }, { keepMarkers: true }));
    compOn.checked = false; store.setComp({ enabled: false }); // it is in the audio now, so switch the live one off
});
$('lim-apply').addEventListener('click', () => { const c = val('lim-ceil'); effect(`Limiter applied (ceiling ${c} dB)`, (b) => store.fxLimit(b, c), { busy: true })(); });
$('gain-apply').addEventListener('click', () => {
    const d = val('gain-db'); if (d === 0) return toast('Move the slider first, then apply.', 'error');
    effect(`Volume ${fmtDb(d)}`, (b) => store.fxGain(b, d))();
});

// live gain-reduction meter
(function grLoop() {
    const gr = compOn.checked && store.isPlaying ? store.getCompReduction() : 0;
    $('gr-fill').style.width = `${clamp(-gr / 20, 0, 1) * 100}%`;
    $('gr-val').textContent = `${gr.toFixed(1)} dB`;
    requestAnimationFrame(grLoop);
})();

// =====================================================================
// Repair
// =====================================================================
bindRange('nr-str', FMT.pct);
bindRange('ds-amt', FMT.pct);
bindRange('gate-thr', FMT.dbPlain);

function setNoiseStatus() {
    const learned = !!store.noiseProfile;
    $('nr-status').textContent = learned ? 'Learned' : 'Auto';
    $('nr-status').classList.toggle('on', learned);
    $('nr-status').title = learned ? 'Click to forget it and go back to automatic' : '';
}
$('nr-status').addEventListener('click', () => { if (store.noiseProfile) { store.noiseProfile = null; setNoiseStatus(); toast('Back to automatic noise detection'); } });
$('nr-learn').addEventListener('click', async () => {
    const r = currentRegion();
    if (!r || r.b - r.a < 0.2) return toast('First select a stretch of just background noise (at least a quarter of a second).', 'error');
    try { await withBusy('Learning the noise...', () => store.learnNoise(r.a, r.b)); setNoiseStatus(); toast('Noise learned. Clear the selection and press Reduce noise.'); }
    catch (e) { toast('That selection is too short to learn from.', 'error'); }
});
$('nr-apply').addEventListener('click', () => {
    const strength = val('nr-str') / 100;
    effect('Noise reduced', (b) => store.fxNoiseReduce(b, { strength, useLearned: true }), { busy: true })();
});
document.querySelectorAll('#hum-seg .seg').forEach((b) => b.addEventListener('click', () => {
    document.querySelectorAll('#hum-seg .seg').forEach((x) => x.classList.toggle('active', x === b));
}));
$('hum-apply').addEventListener('click', () => {
    const hz = +document.querySelector('#hum-seg .seg.active').dataset.hz;
    effect(`${hz} Hz hum removed`, (b) => store.fxHum(b, hz), { busy: true })();
});
$('click-apply').addEventListener('click', () => effect('Clicks and pops removed', (b) => store.fxDeclick(b))());
$('ds-apply').addEventListener('click', () => { const a = val('ds-amt') / 100; effect('Harsh S sounds tamed', (b) => store.fxDeEss(b, a), { busy: true })(); });
$('gate-apply').addEventListener('click', () => { const t = val('gate-thr'); effect('Noise gate applied', (b) => store.fxGate(b, { thresholdDb: t }), { busy: true })(); });

// =====================================================================
// Time: tempo and pitch
// =====================================================================
bindRange('tm-speed', FMT.pct, updateTimeInfo);
bindRange('pt-semi', FMT.st);
document.querySelectorAll('[data-speed]').forEach((b) => b.addEventListener('click', () => {
    $('tm-speed').value = b.dataset.speed; $('tm-speed').dispatchEvent(new Event('input'));
}));
function updateTimeInfo() {
    const el = $('tm-info'); if (!el) return;
    if (!store.audioBuffer) { el.textContent = 'Import audio to begin.'; return; }
    const r = currentRegion(), len = r ? r.b - r.a : D(), sp = val('tm-speed');
    el.textContent = sp === 100 ? 'Drag the slider or pick a preset.' : `${fmtTime(len, 1)} becomes ${fmtTime(len * 100 / sp, 1)}`;
}
$('tm-apply').addEventListener('click', () => {
    const sp = val('tm-speed'); if (sp === 100) return toast('Change the speed first, then apply.', 'error');
    effect(`Tempo set to ${sp}%`, (b) => store.fxTimeStretch(b, 100 / sp), { busy: true, resize: sp / 100 })();
});
$('pt-apply').addEventListener('click', () => {
    const n = val('pt-semi'); if (n === 0) return toast('Move the pitch slider first, then apply.', 'error');
    effect(`Pitch ${n > 0 ? 'raised' : 'lowered'} by ${Math.abs(n)} semitone${Math.abs(n) > 1 ? 's' : ''}`, (b) => store.fxPitchShift(b, n), { busy: true })();
});

// =====================================================================
// Music bed with auto-ducking
// =====================================================================
let musicBuf = null, musicName = '';
bindRange('mu-gain', FMT.db, () => scheduleDraw());
bindRange('mu-duck', FMT.dbPlain, () => scheduleDraw());
bindRange('mu-thr', FMT.dbPlain, () => scheduleDraw());
bindRange('mu-rel', FMT.ms, () => scheduleDraw());
bindRange('mu-fi', FMT.sec);
bindRange('mu-fo', FMT.sec);
$('mu-playhead').addEventListener('change', () => scheduleDraw());

$('music-pick').addEventListener('click', () => { if (!store.audioBuffer) return toast('Import your voice track first.', 'error'); $('music-input').click(); });
$('music-input').addEventListener('change', async (e) => {
    const f = e.target.files[0]; if (!f) return;
    try {
        if (store.ctx.state === 'suspended') await Promise.race([store.ctx.resume(), new Promise((r) => setTimeout(r, 600))]);
        musicBuf = await store.ctx.decodeAudioData(await f.arrayBuffer()); musicName = f.name;
        $('music-file').textContent = `${f.name}  \u00b7  ${fmtTime(musicBuf.duration, 0)}`;
        $('music-file').classList.add('has-file'); scheduleDraw();
        toast('Music added. Adjust the dip, then press Mix into track.');
    } catch (err) { console.error(err); toast("Couldn't read that music file.", 'error'); }
    e.target.value = '';
});
const musicOpts = () => ({
    gainDb: val('mu-gain'), duckDb: val('mu-duck'), thresholdDb: val('mu-thr'), releaseMs: val('mu-rel'),
    fadeIn: val('mu-fi'), fadeOut: val('mu-fo'), loop: $('mu-loop').checked,
    startSec: $('mu-playhead').checked ? store.getCurrentTime() : 0
});
$('mu-apply').addEventListener('click', async () => {
    if (!store.audioBuffer) return toast('Import your voice track first.', 'error');
    if (!musicBuf) return toast('Add a music file first.', 'error');
    const o = musicOpts();
    await withBusy('Mixing the music in...', () => commit('Music mixed in' + (o.duckDb ? ` (dips ${o.duckDb} dB under your voice)` : ''), async () => { await new Promise((r) => setTimeout(r, 20)); store.mixMusic(musicBuf, o); }, { keepMarkers: true }));
});

// the teal curve over the waveform that shows where the music will dip
const duckCanvas = $('duck-canvas');
let duckCache = { key: '', curve: null };
function drawDuck() {
    const g = duckCanvas.getContext('2d');
    if (activeTab !== 'music' || !musicBuf || !store.audioBuffer || waveStyle === 'spectro') {
        if (duckCanvas.width) g.clearRect(0, 0, duckCanvas.width, duckCanvas.height);
        return;
    }
    const dpr = window.devicePixelRatio || 1, w = container.clientWidth, h = container.clientHeight;
    if (w <= 0) return;
    sizeCanvas(duckCanvas, w, h, dpr);
    const o = musicOpts(), key = [o.duckDb, o.thresholdDb, o.releaseMs, store.audioBuffer.length].join('|');
    if (duckCache.key !== key) duckCache = { key, curve: o.duckDb > 0 ? store.duckCurve(store.audioBuffer, o) : null };
    const W = duckCanvas.width, H = duckCanvas.height, top = H * 0.12, bot = H * 0.3;
    g.clearRect(0, 0, W, H);
    const c = duckCache.curve, startX = clamp(frac(o.startSec), 0, 1) * W;
    const yOf = (gain) => top + (1 - gain) * (bot - top) + (1 - 1) * 0;
    g.beginPath(); g.moveTo(startX, yOf(1));
    const frames = c ? c.g.length : 0;
    for (let x = startX; x <= W; x += 2 * dpr) {
        const t = timeAt(x / W);
        let gain = 1;
        if (c) { const f = clamp(Math.floor(t / c.win), 0, frames - 1); gain = c.g[f]; }
        g.lineTo(x, yOf(gain));
    }
    g.lineTo(W, yOf(1)); g.closePath();
    g.fillStyle = `rgba(${TC.rgb_teal},0.16)`; g.fill();
    g.strokeStyle = TC.teal; g.lineWidth = 2 * dpr; g.shadowColor = `rgba(${TC.rgb_teal},.7)`; g.shadowBlur = 8 * dpr; g.stroke(); g.shadowBlur = 0;
    g.fillStyle = `rgba(${TC.rgb_teal},.85)`; g.font = `600 ${11 * dpr}px "Manrope", sans-serif`;
    g.fillText('Music level', startX + 8 * dpr, top - 6 * dpr + 2 * dpr);
}

// =====================================================================
// Tempo and key
// =====================================================================
$('tk-detect').addEventListener('click', async () => {
    if (!store.audioBuffer) return;
    $('tk-bpm').textContent = '...'; $('tk-key').textContent = '...';
    try {
        const [bpm, key] = await withBusy('Listening for tempo and key...', async () => [await store.detectTempo(store.audioBuffer), await store.detectKey(store.audioBuffer)]);
        $('tk-bpm').textContent = bpm ? `${Math.round(bpm.bpm * 10) / 10} BPM` : 'No beat';
        $('tk-key').textContent = key ? key.key : 'Unclear';
        if (!bpm) toast('No steady beat found. That is normal for speech and ambient sound.');
    } catch (e) { console.error(e); $('tk-bpm').textContent = '--'; $('tk-key').textContent = '--'; toast("Couldn't analyse this audio.", 'error'); }
});

// =====================================================================
// Recording (with punch-in over a selection)
// =====================================================================
let rec = null;
function micProblem(e) {
    const onFile = location.protocol === 'file:', tip = onFile ? ' Tip: open the app through a local server (run "python3 -m http.server" in the folder, then visit http://localhost:8000) and your browser will remember the choice.' : '';
    const n = e && e.name;
    if (n === 'NotAllowedError' || n === 'SecurityError' || n === 'PermissionDeniedError')
        return 'Your browser blocked the microphone for this page. Click the lock or site-info icon next to the address, set Microphone to Allow, then press Record again.' + tip;
    if (n === 'NotFoundError' || n === 'DevicesNotFoundError') return 'No microphone was found. Plug one in or pick one in your system sound settings, then try again.';
    if (n === 'NotReadableError' || n === 'AbortError') return 'The microphone is being used by another app. Close it there and try again.';
    return "Couldn't start the microphone (" + (n || 'unknown error') + ')' + tip;
}
async function startRecording() {
    if (rec) return stopRecording();
    if (typeof MediaRecorder === 'undefined' || !navigator.mediaDevices || !navigator.mediaDevices.getUserMedia)
        return toast(window.isSecureContext === false ? 'Recording needs a secure page. Open the app from http://localhost or https.' : 'Recording is not supported in this browser.', 'error', { duration: 7000 });
    let stream;
    const hint = setTimeout(() => toast('Waiting for the microphone. Look near the address bar and press Allow.'), 700);
    $('rec-btn').classList.add('pending');
    try { stream = await navigator.mediaDevices.getUserMedia({ audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false } }); }
    catch (e) { clearTimeout(hint); $('rec-btn').classList.remove('pending'); return toast(micProblem(e), 'error', { duration: 12000 }); }
    clearTimeout(hint); $('rec-btn').classList.remove('pending');
    if (store.isPlaying) togglePlayPause();
    if (store.ctx.state === 'suspended') await Promise.race([store.ctx.resume(), new Promise((r) => setTimeout(r, 600))]);
    const src = store.ctx.createMediaStreamSource(stream), an = store.ctx.createAnalyser(); an.fftSize = 1024; src.connect(an);
    const mime = ['audio/webm;codecs=opus', 'audio/webm', 'audio/mp4', 'audio/ogg'].find((m) => MediaRecorder.isTypeSupported(m));
    const mr = new MediaRecorder(stream, mime ? { mimeType: mime } : undefined), chunks = [], region = store.audioBuffer ? currentRegion() : null;
    mr.ondataavailable = (e) => { if (e.data && e.data.size) chunks.push(e.data); };
    rec = { stream, mr, chunks, an, src, t0: performance.now(), cancelled: false, region: region ? { a: region.a, b: region.b } : null, at: store.audioBuffer ? store.getCurrentTime() : 0, buf: new Float32Array(1024) };
    mr.onstop = () => finishRecording(rec, mime);
    mr.start(250);
    $('rec-btn').classList.add('recording'); $('rec-pill').hidden = false;
    $('rec-label').textContent = rec.region ? 'Punch-in' : 'Recording';
    (function tickRec() {
        if (!rec) return;
        const secs = (performance.now() - rec.t0) / 1000;
        $('rec-time').textContent = `${String(Math.floor(secs / 60)).padStart(2, '0')}:${String(Math.floor(secs % 60)).padStart(2, '0')}`;
        rec.an.getFloatTimeDomainData(rec.buf);
        let p = 0; for (let i = 0; i < rec.buf.length; i++) p = Math.max(p, Math.abs(rec.buf[i]));
        $('rec-level').style.width = `${toMeter(p) * 100}%`;
        requestAnimationFrame(tickRec);
    })();
}
function stopRecording(cancel = false) {
    if (!rec) return;
    rec.cancelled = cancel;
    if (rec.mr.state !== 'inactive') rec.mr.stop();
}
async function finishRecording(r, mime) {
    r.stream.getTracks().forEach((t) => t.stop()); try { r.src.disconnect(); } catch (e) { }
    rec = null; $('rec-btn').classList.remove('recording'); $('rec-pill').hidden = true;
    if (r.cancelled || !r.chunks.length) return toast(r.cancelled ? 'Recording cancelled.' : 'Nothing was recorded.');
    const blob = new Blob(r.chunks, { type: r.mr.mimeType || mime || 'audio/webm' });
    if (!store.audioBuffer) { // first thing in the project: it becomes the track
        await loadFile(new File([blob], 'Recording.webm', { type: blob.type }));
        return;
    }
    try {
        const nb = await store.ctx.decodeAudioData(await blob.arrayBuffer());
        if (r.region) {
            await commit('Recording punched in over your selection', () => store.replaceRegion(r.region.a, r.region.b, nb), { keepMarkers: true });
        } else {
            const at = r.at, add = nb.duration;
            await commit('Recording inserted at the playhead', () => { store.audioBuffer = store.splice(at, at, nb); store.pauseOffset = 0; }, { mapTime: (t) => t >= at ? t + add : t });
        }
        clearSelection();
    } catch (e) { console.error(e); toast("Couldn't process that recording.", 'error'); }
}
$('rec-btn').addEventListener('click', startRecording);
$('rec-stop').addEventListener('click', () => stopRecording());

// =====================================================================
// Clipboard and right-click menu
// =====================================================================
function copySelection(cut = false) {
    const r = currentRegion(); if (!r) return toast('Select something first.', 'error');
    const secs = store.copy(r.a, r.b);
    if (cut) actions.cut(); else toast(`Copied ${secs.toFixed(1)}s`);
}
function pasteAt(t) {
    if (!store.clipboard) return toast('Nothing copied yet. Select audio and press Ctrl/Cmd+C.', 'error');
    const add = store.clipboard.duration;
    commit(`Pasted ${add.toFixed(1)}s`, () => store.paste(t), { mapTime: (x) => x >= t ? x + add : x });
}
function silenceSelection() {
    const r = currentRegion(); if (!r) return toast('Select the part you want to mute.', 'error');
    commit('Selection silenced', () => store.silenceRegion(r.a, r.b), { keepMarkers: true });
}
function insertSilenceAt(t, secs = 1) {
    commit(`Inserted ${secs}s of silence`, () => store.insertSilence(t, secs), { mapTime: (x) => x >= t ? x + secs : x });
}

const ctxMenu = $('ctx-menu');
function hideCtx() { ctxMenu.hidden = true; }
container.addEventListener('contextmenu', (e) => {
    if (!store.audioBuffer) return;
    e.preventDefault();
    const t = timeAt(fracFromEvent(e)), hasSel = !!currentRegion();
    const items = [
        { icon: 'content_cut', label: 'Cut', hint: 'Ctrl X', on: hasSel, run: () => copySelection(true) },
        { icon: 'content_copy', label: 'Copy', hint: 'Ctrl C', on: hasSel, run: () => copySelection(false) },
        { icon: 'content_paste', label: `Paste here`, hint: 'Ctrl V', on: !!store.clipboard, run: () => pasteAt(t) },
        { sep: true },
        { icon: 'volume_off', label: 'Silence selection', on: hasSel, run: silenceSelection },
        { icon: 'hourglass_empty', label: 'Insert 1 second of silence here', on: true, run: () => insertSilenceAt(t, 1) },
        { sep: true },
        { icon: 'flag', label: 'Add marker here', on: true, run: () => { markers.push({ t, name: '' }); markers.sort((a, b) => a.t - b.t); renderMarkers(); } },
        { icon: 'text_select_move_forward_word', label: 'Select this phrase', on: true, run: () => selectPhraseAt(t) },
        { icon: 'select_all', label: 'Select all', on: true, run: actions.selectAll }
    ];
    ctxMenu.innerHTML = '';
    items.forEach((it) => {
        if (it.sep) { const d = document.createElement('div'); d.className = 'ctx-sep'; ctxMenu.appendChild(d); return; }
        const b = document.createElement('button'); b.className = 'ctx-item'; b.disabled = !it.on;
        b.innerHTML = `<span class="material-symbols-rounded">${it.icon}</span><span class="ctx-label"></span>${it.hint ? '<kbd></kbd>' : ''}`;
        b.querySelector('.ctx-label').textContent = it.label; if (it.hint) b.querySelector('kbd').textContent = it.hint;
        b.addEventListener('click', () => { hideCtx(); it.run(); });
        ctxMenu.appendChild(b);
    });
    ctxMenu.hidden = false;
    const mw = ctxMenu.offsetWidth, mh = ctxMenu.offsetHeight;
    ctxMenu.style.left = Math.min(e.clientX, innerWidth - mw - 8) + 'px';
    ctxMenu.style.top = Math.min(e.clientY, innerHeight - mh - 8) + 'px';
});
document.addEventListener('mousedown', (e) => { if (!ctxMenu.contains(e.target)) hideCtx(); });
window.addEventListener('blur', hideCtx);

document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') { hideCtx(); if (rec) stopRecording(true); return; }
    const typing = (e.target.tagName === 'INPUT' && e.target.type === 'text') || e.target.tagName === 'SELECT';
    if (typing || document.querySelector('.modal:not([hidden])')) return;
    const mod = e.metaKey || e.ctrlKey, k = e.key.toLowerCase();
    if (mod && k === 'c') { if (currentRegion()) { e.preventDefault(); copySelection(false); } }
    else if (mod && k === 'x') { if (currentRegion()) { e.preventDefault(); copySelection(true); } }
    else if (mod && k === 'v') { if (store.audioBuffer) { e.preventDefault(); pasteAt(store.getCurrentTime()); } }
    else if (!mod && k === 'r') { e.preventDefault(); startRecording(); }
});

// =====================================================================
// Export dialog (WAV 16/24/32, MP3, selection, chapters)
// =====================================================================
const expModal = $('export-modal');
const clockStr = (t) => { t = Math.max(0, Math.round(t)); const h = Math.floor(t / 3600), m = Math.floor(t % 3600 / 60), s = t % 60; return (h ? `${h}:${String(m).padStart(2, '0')}` : String(m).padStart(2, '0')) + `:${String(s).padStart(2, '0')}`; };
function chaptersText(offset = 0, length = D()) {
    const list = markers.map((m, i) => ({ t: m.t - offset, name: m.name || `Chapter ${i + 1}` })).filter((m) => m.t >= 0 && m.t <= length);
    if (!list.length || list[0].t > 0.5) list.unshift({ t: 0, name: 'Start' });
    return list.map((m) => `${clockStr(m.t)} ${m.name}`).join('\n') + '\n';
}
function exportInfo() {
    const r = $('exp-range').value === 'sel' && currentRegion(), secs = r ? r.b - r.a : D(), f = $('exp-format').value;
    const ch = $('exp-ch').value === 'mono' ? 1 : store.audioBuffer.numberOfChannels, sr = store.audioBuffer.sampleRate;
    const bytes = f.startsWith('mp3') ? secs * parseInt(f.split('-')[1], 10) * 125 : secs * sr * ch * (parseInt(f.slice(3), 10) / 8);
    $('exp-info').textContent = `About ${(bytes / 1048576).toFixed(1)} MB  \u00b7  ${fmtTime(secs, 0)}  \u00b7  ${sr / 1000} kHz`;
}
function openExport() {
    if (!store.audioBuffer) return toast('Nothing to export yet. Import a file first.', 'error');
    const hasSel = !!currentRegion();
    $('exp-range').querySelector('[value=sel]').disabled = !hasSel;
    $('exp-range').value = hasSel ? 'sel' : 'all';
    $('exp-chap').disabled = !markers.length; if (!markers.length) $('exp-chap').checked = false;
    exportInfo(); expModal.hidden = false; $('exp-go').focus();
}
['exp-format', 'exp-ch', 'exp-range'].forEach((id) => $(id).addEventListener('change', exportInfo));
$('exp-cancel').addEventListener('click', () => { expModal.hidden = true; });
expModal.addEventListener('mousedown', (e) => { if (e.target === expModal) expModal.hidden = true; });
document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && !expModal.hidden) expModal.hidden = true; }, true);
$('nav-export').addEventListener('click', openExport);

function download(blob, name) {
    const url = URL.createObjectURL(blob), a = document.createElement('a');
    a.style.display = 'none'; a.href = url; a.download = name; document.body.appendChild(a); a.click();
    setTimeout(() => { document.body.removeChild(a); URL.revokeObjectURL(url); }, 150);
}
$('exp-go').addEventListener('click', async () => {
    const fmt = $('exp-format').value, r = $('exp-range').value === 'sel' ? currentRegion() : null, name = $('project-name-text').innerText;
    expModal.hidden = true;
    try {
        await withBusy('Preparing your file...', async () => {
            let buf = r ? store.extract(r.a, r.b) : store.cloneBuffer(store.audioBuffer);
            if ($('exp-ch').value === 'mono' && buf.numberOfChannels > 1) {
                const m = store.ctx.createBuffer(1, buf.length, buf.sampleRate), d = m.getChannelData(0);
                for (let c = 0; c < buf.numberOfChannels; c++) { const x = buf.getChannelData(c); for (let i = 0; i < d.length; i++) d[i] += x[i] / buf.numberOfChannels; }
                buf = m;
            }
            if ($('exp-norm').checked) {
                let pk = 0; for (let c = 0; c < buf.numberOfChannels; c++) { const x = buf.getChannelData(c); for (let i = 0; i < x.length; i++) pk = Math.max(pk, Math.abs(x[i])); }
                if (pk > 0) { const g = Math.pow(10, -1 / 20) / pk; for (let c = 0; c < buf.numberOfChannels; c++) { const x = buf.getChannelData(c); for (let i = 0; i < x.length; i++) x[i] *= g; } }
            }
            const suffix = r ? '_selection' : '_Export';
            if (fmt.startsWith('mp3')) download(await store.encodeMP3(buf, parseInt(fmt.split('-')[1], 10)), `${name}${suffix}.mp3`);
            else download(store.encodeWAV(buf, parseInt(fmt.slice(3), 10)), `${name}${suffix}.wav`);
            if ($('exp-chap').checked) download(new Blob([chaptersText(r ? r.a : 0, buf.duration)], { type: 'text/plain' }), `${name}_chapters.txt`);
        });
        toast('Exported ' + (fmt.startsWith('mp3') ? 'MP3' : 'WAV'));
    } catch (err) { console.error(err); toast(err.message || "Couldn't export that file.", 'error'); }
});

// =====================================================================
// Session autosave and restore (IndexedDB)
// =====================================================================
const idbOpen = () => new Promise((res, rej) => {
    const r = indexedDB.open('chronos-pro', 1);
    r.onupgradeneeded = () => r.result.createObjectStore('session');
    r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error);
});
const idbGet = async () => { const db = await idbOpen(); return new Promise((res, rej) => { const q = db.transaction('session').objectStore('session').get('last'); q.onsuccess = () => res(q.result); q.onerror = () => rej(q.error); }); };
const idbPut = async (v) => { const db = await idbOpen(); return new Promise((res, rej) => { const t = db.transaction('session', 'readwrite'); t.objectStore('session').put(v, 'last'); t.oncomplete = res; t.onerror = () => rej(t.error); }); };
const packBuf = (b) => ({ sr: b.sampleRate, ch: Array.from({ length: b.numberOfChannels }, (_, c) => b.getChannelData(c).slice().buffer) });
const unpackBuf = (p) => { const b = store.ctx.createBuffer(p.ch.length, new Float32Array(p.ch[0]).length, p.sr); p.ch.forEach((a, c) => b.copyToChannel(new Float32Array(a), c)); return b; };

let saveTimer = null;
function scheduleAutosave() { clearTimeout(saveTimer); saveTimer = setTimeout(saveSession, 1500); }
async function saveSession() {
    const b = store.audioBuffer, o = store.originalBuffer; if (!b) return;
    if ((b.length + (o ? o.length : 0)) * b.numberOfChannels * 4 > 400e6) return; // too big to keep safely
    try { await idbPut({ name: $('project-name-text').innerText, assets, markers, cur: packBuf(b), orig: o ? packBuf(o) : null, saved: Date.now() }); } catch (e) { console.warn('Autosave skipped', e); }
}
async function restoreSession(saved) {
    saved = saved || await idbGet(); if (!saved) return toast('No saved session found.', 'error');
    store.audioBuffer = unpackBuf(saved.cur);
    store.originalBuffer = saved.orig ? unpackBuf(saved.orig) : store.cloneBuffer(store.audioBuffer);
    store.history = []; store.redoStack = []; store.pauseOffset = 0; store.resetEQ();
    $('project-name-text').innerText = saved.name || 'Podcast_Edit_v05';
    resetPlayState(); sel = null; silences = []; markers = (saved.markers || []).map((m) => (typeof m === 'number' ? { t: m, name: '' } : m));
    assets = saved.assets && saved.assets.length ? saved.assets : [{ name: 'Restored session', appended: false }]; renderAssets();
    setHasAudio(true); bufferChanged(false);
    toast('Session restored');
}
(async function offerRestore() {
    try {
        const saved = await idbGet();
        if (saved && !store.audioBuffer) {
            const mins = Math.max(0, Math.round((Date.now() - saved.saved) / 60000)), secs = saved.cur.ch[0].byteLength / 4 / saved.cur.sr;
            toast(`Pick up where you left off? "${saved.name}" (${fmtTime(secs, 0)}, saved ${mins < 1 ? 'just now' : mins + ' min ago'})`, 'ok',
                { duration: 15000, action: { label: 'Restore', icon: 'history', run: () => restoreSession(saved) } });
        }
    } catch (e) { /* storage unavailable: autosave just stays off */ }
})();

// =====================================================================
// Hooks called by main.js
// =====================================================================
function onBufferChanged() { updateTimeInfo(); scheduleAutosave(); }
function onFileLoaded() { store.noiseProfile = null; setNoiseStatus(); updateScopeNotes(); }
function onTabChanged(name) { drawDuck(); updateScopeNotes(); }

// extra entries for the Ctrl/Cmd+K palette
function extraCommands() {
    return [
        { name: 'Record from microphone', icon: 'mic', hint: 'R', run: startRecording },
        { name: 'Copy selection', icon: 'content_copy', hint: isMac ? '\u2318C' : 'Ctrl C', run: () => copySelection(false) },
        { name: 'Paste at playhead', icon: 'content_paste', hint: isMac ? '\u2318V' : 'Ctrl V', run: () => pasteAt(store.getCurrentTime()) },
        { name: 'Silence selection', icon: 'volume_off', hint: '', run: silenceSelection },
        { name: 'Insert 1 second of silence at playhead', icon: 'hourglass_empty', hint: '', run: () => insertSilenceAt(store.getCurrentTime(), 1) },
        { name: 'Reduce background noise', icon: 'noise_control_off', hint: 'Repair', run: () => { setTab('repair'); $('nr-apply').click(); } },
        { name: 'Remove clicks and pops', icon: 'auto_fix_high', hint: 'Repair', run: () => $('click-apply').click() },
        { name: 'Open dynamics (compressor, limiter)', icon: 'compress', hint: 'Panel', run: () => setTab('dynamics') },
        { name: 'Open repair tools', icon: 'healing', hint: 'Panel', run: () => setTab('repair') },
        { name: 'Open tempo and pitch', icon: 'speed', hint: 'Panel', run: () => setTab('time') },
        { name: 'Open music bed (auto-duck)', icon: 'library_music', hint: 'Panel', run: () => setTab('music') },
        { name: 'Detect tempo and key', icon: 'music_note', hint: 'Analyze', run: () => { setTab('analyze'); $('tk-detect').click(); } },
        { name: 'Export audio...', icon: 'download', hint: '', run: openExport },
        { name: 'Restore last saved session', icon: 'history', hint: '', run: () => restoreSession() }
    ];
}

updateScopeNotes();
setNoiseStatus();

// ---------- "there is more below" cue for long panels ----------
function updateScrollHint() {
    const panel = document.querySelector('.tabs-panel'), pane = document.querySelector('.tab-pane:not([hidden])');
    if (!panel || !pane) return;
    panel.classList.toggle('more', pane.scrollHeight > pane.clientHeight + 4 && pane.scrollTop + pane.clientHeight < pane.scrollHeight - 6);
}
document.querySelectorAll('.tab-pane').forEach((p) => p.addEventListener('scroll', updateScrollHint));
window.addEventListener('resize', updateScrollHint);
document.querySelectorAll('.tab').forEach((t) => t.addEventListener('click', () => setTimeout(updateScrollHint, 30)));
new ResizeObserver(updateScrollHint).observe(document.querySelector('.tabs-panel'));
setTimeout(updateScrollHint, 100);

// =====================================================================
// Design layer: themes, welcome screen, demo song, Voice/Music mode, shortcuts
// =====================================================================

// ---------- colour themes ----------
const THEMES = [
    { id: 'aurora', name: 'Aurora', sw: ['#5ee6d4', '#ffb547', '#8bd3ff'] },
    { id: 'sunset', name: 'Sunset', sw: ['#ff6fa5', '#ffc857', '#ffb199'] },
    { id: 'neon', name: 'Neon', sw: ['#b388ff', '#ff4fd0', '#5ee1ff'] },
    { id: 'vinyl', name: 'Vinyl', sw: ['#e5b869', '#ff8a3d', '#f5dfb3'] }
];
const currentTheme = () => document.documentElement.getAttribute('data-theme') || 'aurora';
function setTheme(id, announce = true) {
    const t = THEMES.find((x) => x.id === id) || THEMES[0];
    if (t.id === 'aurora') document.documentElement.removeAttribute('data-theme'); else document.documentElement.setAttribute('data-theme', t.id);
    try { localStorage.setItem('chronos-theme', t.id === 'aurora' ? '' : t.id); } catch (e) { }
    readTheme();
    if (store.audioBuffer) { drawOverview(); scheduleDraw(); }
    if (announce) toast(`Theme: ${t.name}`);
}
const themeMenu = $('theme-menu');
$('theme-btn').addEventListener('click', (e) => {
    e.stopPropagation();
    if (!themeMenu.hidden) { themeMenu.hidden = true; return; }
    themeMenu.innerHTML = '';
    THEMES.forEach((t) => {
        const b = document.createElement('button');
        b.className = 'theme-item' + (t.id === currentTheme() ? ' current' : '');
        b.innerHTML = `<span class="theme-swatch">${t.sw.map((c) => `<i style="background:${c}"></i>`).join('')}</span><span>${t.name}</span><span class="material-symbols-rounded check">check</span>`;
        b.addEventListener('click', () => { themeMenu.hidden = true; setTheme(t.id); });
        themeMenu.appendChild(b);
    });
    const r = $('theme-btn').getBoundingClientRect();
    themeMenu.hidden = false;
    themeMenu.style.top = (r.bottom + 8) + 'px';
    themeMenu.style.left = Math.min(r.left, innerWidth - themeMenu.offsetWidth - 10) + 'px';
});
document.addEventListener('mousedown', (e) => { if (!themeMenu.contains(e.target) && e.target.closest('#theme-btn') === null) themeMenu.hidden = true; });
readTheme();

// ---------- welcome screen: flowing light ribbons that follow the cursor ----------
const heroCanvas = $('hero-canvas'), heroStage = $('empty-stage');
const heroMouse = { x: 0.5, y: 0.5, on: false };
heroStage.addEventListener('mousemove', (e) => { const r = heroCanvas.getBoundingClientRect(); heroMouse.x = (e.clientX - r.left) / r.width; heroMouse.y = (e.clientY - r.top) / r.height; heroMouse.on = true; });
heroStage.addEventListener('mouseleave', () => { heroMouse.on = false; });
const heroDots = Array.from({ length: 48 }, () => ({ x: Math.random(), y: Math.random(), s: Math.random() * 1.6 + 0.5, v: Math.random() * 0.025 + 0.006, p: Math.random() * 6.28 }));
const HERO_RIBBONS = [
    { c: 'teal', f: 1.1, s: 0.7, a: 0.15, y: 0.8 }, { c: 'ice', f: 1.7, s: -0.9, a: 0.12, y: 0.82 }, { c: 'amber', f: 2.4, s: 1.1, a: 0.09, y: 0.79 },
    { c: 'rose', f: 3.3, s: -1.4, a: 0.07, y: 0.81 }, { c: 'teal', f: 0.7, s: 0.4, a: 0.19, y: 0.84 }
];
let heroPhase = 0, heroLast = 0, heroPaused = false;
function heroFrame(ts) {
    requestAnimationFrame(heroFrame);
    if (store.audioBuffer || heroPaused) return;
    const w = heroCanvas.clientWidth, h = heroCanvas.clientHeight; if (w <= 0 || h <= 0) return;
    const dpr = window.devicePixelRatio || 1; sizeCanvas(heroCanvas, w, h, dpr);
    const g = heroCanvas.getContext('2d'), W = heroCanvas.width, H = heroCanvas.height;
    const dt = Math.min(0.05, (ts - heroLast) / 1000 || 0.016); heroLast = ts;
    heroPhase += dt * (0.55 + (heroMouse.on ? 0.5 : 0));
    g.clearRect(0, 0, W, H);
    // floating dust
    heroDots.forEach((d) => {
        d.y -= d.v * dt; if (d.y < -0.02) { d.y = 1.02; d.x = Math.random(); }
        const a = 0.15 + 0.35 * (0.5 + 0.5 * Math.sin(heroPhase * 1.5 + d.p));
        g.fillStyle = `rgba(${TC.rgb_ice},${a.toFixed(3)})`; g.beginPath(); g.arc(d.x * W, d.y * H, d.s * dpr, 0, 6.283); g.fill();
    });
    // ribbons
    g.globalCompositeOperation = 'lighter'; g.lineJoin = 'round';
    HERO_RIBBONS.forEach((r, i) => {
        const breathe = 0.7 + 0.3 * Math.sin(heroPhase * 0.9 + i), path = new Path2D();
        for (let x = 0; x <= W; x += 6 * dpr) {
            const u = x / W, env = Math.pow(Math.sin(Math.PI * u), 1.1);
            const bump = heroMouse.on ? Math.exp(-Math.pow(u - heroMouse.x, 2) / 0.025) * 0.9 : 0;
            const amp = H * r.a * breathe * (1 + bump * 1.4);
            const y = H * r.y + (heroMouse.on ? (heroMouse.y - 0.5) * H * 0.18 * bump : 0)
                + env * amp * (Math.sin(u * 6.283 * r.f + heroPhase * r.s + i) + 0.45 * Math.sin(u * 6.283 * r.f * 2.2 - heroPhase * r.s * 0.7));
            x === 0 ? path.moveTo(x, y) : path.lineTo(x, y);
        }
        const rgb = TC['rgb_' + r.c];
        g.strokeStyle = `rgba(${rgb},0.10)`; g.lineWidth = 12 * dpr; g.stroke(path);
        g.strokeStyle = `rgba(${rgb},0.55)`; g.lineWidth = 1.8 * dpr; g.stroke(path);
    });
    g.globalCompositeOperation = 'source-over';
}
requestAnimationFrame(heroFrame);

$('hero-rec-btn').addEventListener('click', startRecording);

// ---------- demo song ----------
async function loadDemo() {
    if (store.audioBuffer) {
        const ok = await openModal({ title: 'Load the demo song?', message: 'This replaces what is open now. Your current work stays saved in History until you close the page.', confirmLabel: 'Load demo' });
        if (!ok) return;
    }
    heroPaused = true; // give the CPU to the synth for a moment
    await withBusy('Synthesizing the demo song...', async () => {
        if (store.ctx.state === 'suspended') await Promise.race([store.ctx.resume(), new Promise((r) => setTimeout(r, 600))]);
        const b = await store.makeDemo();
        await loadFile(new File([store.encodeWAV(b, 16)], 'Midnight Drive (demo).wav', { type: 'audio/wav' }));
    });
    heroPaused = false;
    if (store.audioBuffer) {
        $('project-name-text').innerText = 'Midnight_Drive_Demo';
        setWaveStyle('live');
        togglePlayPause();
    }
}
$('demo-btn').addEventListener('click', loadDemo);

// ---------- one-click button: Voice or Music ----------
let polishMode = 'voice';
try { polishMode = localStorage.getItem('chronos-polish') || 'voice'; } catch (e) { }
const polishVoice = effect('Podcast polish applied', (b) => store.polish(b), { busy: true });
const polishMusic = effect('Music master applied', (b) => store.masterMusic(b), { busy: true });
fxList.polish = () => (polishMode === 'music' ? polishMusic : polishVoice)();
fxList.master = polishMusic;
function setPolishMode(m) {
    polishMode = m;
    document.querySelectorAll('#polish-mode .seg').forEach((b) => b.classList.toggle('active', b.dataset.mode === m));
    const music = m === 'music';
    $('polish-title').textContent = music ? 'Music master' : 'Podcast polish';
    $('polish-sub').textContent = music ? 'One-click loud master' : 'One-click voice cleanup';
    $('polish-icon').textContent = music ? 'album' : 'auto_awesome';
    $('polish-btn').title = music ? 'Tidy the lows, add air, glue-compress, then raise to streaming loudness with safe peaks'
        : 'High-pass, de-mud, add presence and air, compress, then level to -16 LUFS';
    try { localStorage.setItem('chronos-polish', m); } catch (e) { }
}
document.querySelectorAll('#polish-mode .seg').forEach((b) => b.addEventListener('click', () => setPolishMode(b.dataset.mode)));
setPolishMode(polishMode);

// ---------- keyboard shortcuts sheet ----------
const mod = isMac ? '\u2318' : 'Ctrl';
const SHORTCUTS = [
    ['Playback', [['Play / pause', 'Space'], ['Loop', 'L'], ['Record', 'R'], ['Add marker', 'M'], ['Previous / next marker', ', .']]],
    ['Editing', [['Undo', `${mod} Z`], ['Redo', `${mod} Shift Z`], ['Copy / cut / paste', `${mod} C X V`], ['Cut selection', 'Delete'], ['Select all', `${mod} A`], ['Clear selection', 'Esc']]],
    ['View', [['Zoom in / out', '+ -'], ['Fit whole track', '0'], ['Search every action', `${mod} K`], ['This sheet', '?']]],
    ['With the mouse', [['Select a phrase', 'Double-click'], ['Zoom', 'Scroll'], ['Cut, copy, paste menu', 'Right-click'], ['Name a marker', 'Double-click it']]]
];
function buildShortcuts() {
    const grid = $('sc-grid'); grid.innerHTML = '';
    SHORTCUTS.forEach(([title, rows]) => {
        const h = document.createElement('div'); h.className = 'sc-head'; h.textContent = title; grid.appendChild(h);
        rows.forEach(([label, keys]) => {
            const r = document.createElement('div'); r.className = 'sc-row';
            r.innerHTML = '<span></span><kbd></kbd>'; r.firstChild.textContent = label; r.lastChild.textContent = keys; grid.appendChild(r);
        });
    });
}
buildShortcuts();
const scModal = $('shortcuts-modal');
const openShortcuts = () => { scModal.hidden = false; $('sc-close').focus(); };
$('sc-close').addEventListener('click', () => { scModal.hidden = true; });
scModal.addEventListener('mousedown', (e) => { if (e.target === scModal) scModal.hidden = true; });
document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && !scModal.hidden) { scModal.hidden = true; return; }
    const typing = (e.target.tagName === 'INPUT' && e.target.type === 'text') || e.target.tagName === 'SELECT';
    if (e.key === '?' && !typing && $('modal').hidden && $('palette').hidden && $('export-modal').hidden) { e.preventDefault(); scModal.hidden ? openShortcuts() : (scModal.hidden = true); }
}, true);

// ---------- "continue where you left off" card on the welcome screen ----------
(async function heroResume() {
    try {
        const saved = await idbGet(); if (!saved || store.audioBuffer) return;
        const secs = saved.cur.ch[0].byteLength / 4 / saved.cur.sr, box = $('hero-resume');
        box.hidden = false; box.innerHTML = '<span></span><button>Continue</button>';
        box.firstChild.textContent = `Pick up where you left off: ${saved.name} (${fmtTime(secs, 0)})`;
        box.lastChild.addEventListener('click', () => restoreSession(saved));
    } catch (e) { }
})();

// extend the Ctrl/Cmd+K palette
const _extraCommands = extraCommands;
extraCommands = function () {
    return [
        ..._extraCommands(),
        { name: 'Load the demo song', icon: 'play_circle', hint: 'Try it', run: loadDemo },
        { name: 'Music master (one click)', icon: 'album', hint: 'Music', run: () => { setPolishMode('music'); fxList.master(); } },
        { name: 'Podcast polish (one click)', icon: 'auto_awesome', hint: 'Voice', run: () => { setPolishMode('voice'); fxList.polish(); } },
        { name: 'Keyboard shortcuts', icon: 'keyboard', hint: '?', run: openShortcuts },
        ...THEMES.map((t) => ({ name: `Theme: ${t.name}`, icon: 'palette', hint: 'Look', run: () => setTheme(t.id) }))
    ];
};


// =====================================================================
// Master studio: pick a style, hear before/after, then apply
// =====================================================================
const MASTER_PRESETS = [
    { id: 'streaming', name: 'Streaming', about: 'Balanced and clear at -14 LUFS (Spotify, Apple Music, YouTube)', target: -14, low: [90, 1.5], mud: -1.5, pres: 1, air: [9500, 2.5], comp: 0.5, width: 1.05 },
    { id: 'loud', name: 'Loud', about: 'Punchy and dense at -9 LUFS, for clubs and hard-hitting genres', target: -9, ceiling: -0.8, low: [80, 2.5], mud: -2, pres: 1.5, air: [9000, 3], comp: 1, width: 1.15 },
    { id: 'warm', name: 'Warm', about: 'Fuller lows and softer highs at -14 LUFS', target: -14, low: [110, 2.5], mud: -1, pres: 0, air: [8500, -1.5], comp: 0.4, width: 1 },
    { id: 'bright', name: 'Bright', about: 'Open and airy highs at -14 LUFS', target: -14, low: [90, 0], mud: -1, pres: 2, air: [8000, 4], comp: 0.45, width: 1.1 },
    { id: 'gentle', name: 'Gentle', about: 'Light touch at -16 LUFS that keeps the dynamics', target: -16, low: [90, 0.5], mud: -0.5, pres: 0.5, air: [10000, 1], comp: 0.25, width: 1 },
    { id: 'voice', name: 'Voice', about: 'Podcast cleanup: presence, air and -16 LUFS', target: -16, voice: true }
];
const MP = { open: false, orig: null, result: null, which: 'b', preset: 'streaming', amt: 1, ready: false, token: 0, applying: false, before: null, after: null, gainB: 1 };
const mpEl = $('master-panel');

function lufsText(m) { return m && isFinite(m.lufs) ? `${m.lufs.toFixed(1)} LUFS` : '-- LUFS'; }
function updateMasterUI() {
    const p = MASTER_PRESETS.find((x) => x.id === MP.preset);
    document.querySelectorAll('#mp-presets .chip').forEach((c) => c.classList.toggle('active', c.dataset.preset === MP.preset));
    $('mp-about').textContent = MP.ready ? p.about : 'Mastering...';
    document.querySelectorAll('#mp-ab .seg').forEach((b) => { b.classList.toggle('active', b.dataset.ab === MP.which); b.disabled = !MP.ready; });
    $('mp-a-lufs').textContent = lufsText(MP.before); $('mp-a-peak').textContent = MP.before && isFinite(MP.before.peakDb) ? `peak ${MP.before.peakDb.toFixed(1)} dB` : '';
    $('mp-b-lufs').textContent = MP.ready ? lufsText(MP.after) : '...'; $('mp-b-peak').textContent = MP.ready && MP.after && isFinite(MP.after.peakDb) ? `peak ${MP.after.peakDb.toFixed(1)} dB` : '';
    $('mp-card-a').classList.toggle('on', MP.which === 'a'); $('mp-card-b').classList.toggle('on', MP.which === 'b');
    $('mp-apply').disabled = !MP.ready; $('mp-amt').disabled = !!p.voice;
    mpEl.classList.toggle('busy', !MP.ready);
}
function masterUse(which) { // switch what you hear (and see), without losing your place
    const buf = which === 'a' ? MP.orig : MP.result; if (!buf) return;
    MP.which = which;
    const wasPlaying = store.isPlaying; if (wasPlaying) store.pause();
    store.audioBuffer = buf;
    store.abGain.gain.value = (which === 'b' && $('mp-match').checked) ? MP.gainB : 1;
    if (wasPlaying) store.play();
    drawOverview(); scheduleDraw(); updateMasterUI();
}
async function masterRender() {
    const tk = ++MP.token; MP.ready = false; updateMasterUI();
    await new Promise((r) => setTimeout(r, 20));
    const p = MASTER_PRESETS.find((x) => x.id === MP.preset);
    let res;
    try { res = await store.masterWith(MP.orig, p, MP.amt); }
    catch (e) { console.error(e); if (tk === MP.token) { toast("Mastering didn't work on this audio.", 'error'); closeMaster(true); } return; }
    if (tk !== MP.token || !MP.open) return;
    MP.result = res; MP.after = store.measureLoudness(res);
    MP.gainB = isFinite(MP.before.lufs) && isFinite(MP.after.lufs) ? clamp(Math.pow(10, (MP.before.lufs - MP.after.lufs) / 20), 0.3, 2.2) : 1;
    MP.ready = true; masterUse(MP.which);
}
async function openMaster() {
    if (MP.open) return;
    if (!store.audioBuffer) {
        await loadDemo(); if (!store.audioBuffer) return;
        toast('Loaded the demo song so you can hear what mastering does.');
    }
    if (rec) return toast('Stop the recording first.', 'error');
    MP.open = true; MP.orig = store.audioBuffer; MP.result = null; MP.which = 'b'; MP.ready = false; MP.applying = false;
    MP.before = store.measureLoudness(MP.orig);
    mpEl.hidden = false; $('master-btn').classList.add('on'); document.body.classList.add('master-open'); updateMasterUI();
    await masterRender();
}
function closeMaster(restore = true) {
    if (!MP.open) return;
    MP.token++;
    if (restore && MP.orig && store.audioBuffer !== MP.orig) {
        const wasPlaying = store.isPlaying; if (wasPlaying) store.pause();
        store.audioBuffer = MP.orig; if (wasPlaying) store.play();
    }
    store.abGain.gain.value = 1;
    MP.open = false; MP.result = null; mpEl.hidden = true; $('master-btn').classList.remove('on'); document.body.classList.remove('master-open');
    if (store.audioBuffer) { drawOverview(); scheduleDraw(); }
}
function masterGuard() { if (MP.open && !MP.applying) closeMaster(true); }
async function applyMaster() {
    if (!MP.ready || !MP.open) return;
    const result = MP.result, name = MASTER_PRESETS.find((x) => x.id === MP.preset).name, wasPlaying = store.isPlaying;
    MP.applying = true;
    if (wasPlaying) store.pause();
    store.audioBuffer = MP.orig; store.abGain.gain.value = 1;       // commit must snapshot the original
    await commit(`Mastered (${name})`, () => { store.audioBuffer = result; }, { keepMarkers: true });
    closeMaster(false); MP.applying = false;
    if (wasPlaying) store.play();
}
// build the style chips once
MASTER_PRESETS.forEach((p) => {
    const b = document.createElement('button'); b.className = 'chip'; b.dataset.preset = p.id; b.textContent = p.name; b.title = p.about;
    b.addEventListener('click', () => { if (MP.preset === p.id && MP.ready) return; MP.preset = p.id; masterRender(); });
    $('mp-presets').appendChild(b);
});
let mpTimer;
$('mp-amt').addEventListener('input', (e) => { MP.amt = e.target.value / 100; $('mp-amt-out').textContent = e.target.value + '%'; setSliderFill(e.target); clearTimeout(mpTimer); mpTimer = setTimeout(masterRender, 350); });
setSliderFill($('mp-amt')); $('mp-amt-out').textContent = '100%';
document.querySelectorAll('#mp-ab .seg').forEach((b) => b.addEventListener('click', () => masterUse(b.dataset.ab)));
$('mp-match').addEventListener('change', () => masterUse(MP.which));
$('mp-apply').addEventListener('click', applyMaster);
$('mp-cancel').addEventListener('click', () => closeMaster(true));
$('mp-close').addEventListener('click', () => closeMaster(true));
$('master-btn').addEventListener('click', () => (MP.open ? closeMaster(true) : openMaster()));
document.addEventListener('keydown', (e) => {
    if (!MP.open) return;
    const typing = (e.target.tagName === 'INPUT' && e.target.type === 'text') || e.target.tagName === 'SELECT';
    if (typing || document.querySelector('.modal:not([hidden])')) return;
    if (!e.metaKey && !e.ctrlKey && e.key.toLowerCase() === 'b' && MP.ready) { e.preventDefault(); masterUse(MP.which === 'a' ? 'b' : 'a'); }
    else if (e.key === 'Escape') closeMaster(true);
});

// ---------- the welcome actions, available on the main screen too ----------
$('asset-rec').addEventListener('click', startRecording);
$('asset-demo').addEventListener('click', loadDemo);
document.querySelectorAll('.hero-card').forEach((c) => c.addEventListener('click', async () => {
    const act = c.dataset.act;
    if (act === 'master') openMaster();
    else if (act === 'repair') { setTab('repair'); toast('Load a recording or the demo song, then use these repair tools.'); }
    else if (act === 'music') { setTab('music'); toast('Load your voice track first, then add music that dips for you.'); }
    else if (act === 'see') { await loadDemo(); if (store.audioBuffer) setWaveStyle('spectro'); }
}));

// extend the palette once more
const _extra2 = extraCommands;
extraCommands = function () {
    return [
        { name: 'Master: compare before and after', icon: 'auto_awesome', hint: 'Master', run: openMaster },
        ..._extra2()
    ];
};


// =====================================================================
// Add a song to the end with a crossfade
// =====================================================================
const apModal = $('append-modal'), apLen = $('ap-len'), apCanvas = $('ap-canvas');
let ap = null; // { file, nb, resolve, curve }

function apCurrent() { return { x: +apLen.value, curve: ap ? ap.curve : 'equal' }; }
function apDraw() {
    const dpr = window.devicePixelRatio || 1, w = apCanvas.clientWidth, h = apCanvas.clientHeight; if (w <= 0) return;
    sizeCanvas(apCanvas, w, h, dpr);
    const g = apCanvas.getContext('2d'); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
    const { x, curve } = apCurrent(), pad = 14, top = 12, bot = h - 20, a = store.audioBuffer.duration, b = ap.nb.duration;
    // timeline: last stretch of song 1, then song 2; the overlap is highlighted
    const before = Math.min(a, Math.max(x * 1.6, 6)), after = Math.min(b, Math.max(x * 1.6, 6)), total = before + after - x;
    const X = (t) => pad + (t / total) * (w - 2 * pad), s1 = X(0), o0 = X(before - x), o1 = X(before);
    g.fillStyle = `rgba(${TC.rgb_amber},0.12)`; g.fillRect(o0, top, Math.max(2, o1 - o0), bot - top);
    const line = (fn, color) => {
        g.beginPath();
        for (let i = 0; i <= 60; i++) { const t = i / 60, px = o0 + (o1 - o0) * t, py = bot - fn(t) * (bot - top); i ? g.lineTo(px, py) : g.moveTo(px, py); }
        g.strokeStyle = color; g.lineWidth = 2.5; g.stroke();
    };
    // flat parts outside the overlap
    g.strokeStyle = TC.rose; g.lineWidth = 2.5; g.beginPath(); g.moveTo(s1, top); g.lineTo(o0, top); g.stroke();
    g.strokeStyle = TC.teal; g.beginPath(); g.moveTo(o1, top); g.lineTo(pad + (w - 2 * pad), top); g.stroke();
    if (x > 0) {
        line(curve === 'linear' ? (t) => 1 - t : (t) => Math.cos(t * Math.PI / 2), TC.rose);
        line(curve === 'linear' ? (t) => t : (t) => Math.sin(t * Math.PI / 2), TC.teal);
    } else { g.strokeStyle = TC.amber; g.setLineDash([4, 4]); g.beginPath(); g.moveTo(o0, top); g.lineTo(o0, bot); g.stroke(); g.setLineDash([]); }
    g.font = '600 10px "Manrope", sans-serif'; g.textBaseline = 'alphabetic';
    g.fillStyle = TC.rose; g.fillText('Song 1', s1 + 2, h - 6);
    g.fillStyle = TC.teal; g.textAlign = 'right'; g.fillText('Song 2', w - pad, h - 6);
    g.fillStyle = TC.amber; g.textAlign = 'center'; g.fillText(x > 0 ? `${x}s blend` : 'straight cut', (o0 + o1) / 2, h - 6); g.textAlign = 'left';
}
function apUpdate() {
    const { x } = apCurrent(), a = store.audioBuffer.duration, b = ap.nb.duration;
    $('ap-len-out').textContent = x === 0 ? 'None' : `${x}s`; setSliderFill(apLen);
    $('ap-info').textContent = x === 0
        ? `Result ${fmtTime(a + b, 1)}  \u00b7  the new song starts right after the first ends`
        : `Result ${fmtTime(a + b - x, 1)}  \u00b7  the songs overlap from ${fmtTime(a - x, 1)}`;
    apDraw();
}
function askAppend(file, nb) {
    return new Promise((resolve) => {
        const a = store.audioBuffer.duration, limit = Math.max(0, Math.floor(Math.min(12, Math.min(a, nb.duration) * 0.9) * 2) / 2);
        let saved = 4; try { const v = parseFloat(localStorage.getItem('chronos-xfade')); if (isFinite(v)) saved = v; } catch (e) { }
        apLen.max = limit; apLen.value = Math.min(saved, limit);
        ap = { file, nb, resolve, curve: 'equal' };
        document.querySelectorAll('#ap-curve .seg').forEach((b) => b.classList.toggle('active', b.dataset.curve === 'equal'));
        $('ap-file').textContent = `${file.name}  \u00b7  ${fmtTime(nb.duration, 0)}`;
        apModal.hidden = false; apUpdate(); apLen.focus(); // slider, not the button, so a stray Space cannot confirm
    });
}
function closeAppend(result) {
    if (!ap) return;
    const r = ap.resolve; apModal.hidden = true; ap = null; r(result);
}
apLen.addEventListener('input', () => { if (ap) apUpdate(); });
document.querySelectorAll('#ap-curve .seg').forEach((b) => b.addEventListener('click', () => {
    if (!ap) return; ap.curve = b.dataset.curve;
    document.querySelectorAll('#ap-curve .seg').forEach((x) => x.classList.toggle('active', x === b)); apUpdate();
}));
$('ap-cancel').addEventListener('click', () => closeAppend(null));
apModal.addEventListener('mousedown', (e) => { if (e.target === apModal) closeAppend(null); });
$('ap-go').addEventListener('click', () => closeAppend({ crossfade: +apLen.value, curve: ap.curve, matchLoudness: $('ap-match').checked, marker: $('ap-marker').checked }));
document.addEventListener('keydown', (e) => {
    if (!ap) return;
    if (e.key === 'Escape') { e.stopPropagation(); closeAppend(null); }
    else if (e.key === 'Enter' && e.target.tagName !== 'BUTTON') { e.preventDefault(); $('ap-go').click(); }
}, true);
window.addEventListener('resize', () => { if (ap) apDraw(); });

async function appendWithDialog(file, nb) {
    const opts = await askAppend(file, nb);
    if (!opts) { toast('Nothing was added.'); return false; }
    try { localStorage.setItem('chronos-xfade', String(opts.crossfade)); } catch (e) { }
    let info = null;
    const label = `Added ${file.name}` + (opts.crossfade > 0 ? ` with a ${opts.crossfade}s crossfade` : '');
    await commit(label, () => { info = store.appendAudio(nb, opts); }, { keepMarkers: true });
    if (!info) return false;
    if (opts.marker) {
        const name = file.name.replace(/\.[^.]+$/, '').slice(0, 28);
        markers.push({ t: info.joinStart, name }); markers.sort((x, y) => x.t - y.t); renderMarkers();
    }
    assets.push({ name: file.name, appended: true }); renderAssets(); clearSelection();
    return true;
}

const _extra3 = extraCommands;
extraCommands = function () {
    return [{ name: 'Add a song with a crossfade', icon: 'library_add', hint: 'Append', run: () => $('merge-btn').click() }, ..._extra3()];
};


// =====================================================================
// Playback speed and device preview (used by the Lyrics panel and the Release check)
// =====================================================================
AudioStore.prototype.setRate = function (r) {
    r = Math.max(0.25, Math.min(4, +r || 1));
    const t = this.getCurrentTime();           // song time, measured at the old speed
    this.rate = r;
    if (this.sourceNode) {
        this.sourceNode.playbackRate.value = r;
        if (this.isPlaying) this.startTime = this.ctx.currentTime - t / r;
    }
};
// Rough frequency/stereo behaviour of common playback devices, so a mix can be checked before release
const DEVICE_PROFILES = {
    phone: { mono: true, hp: 380, lp: 11000, peaks: [[2800, 1.2, 2.5]], comp: true },
    speaker: { mono: false, hp: 85, lp: 13000, shelves: [['lowshelf', 160, 4]], peaks: [[1500, 1, -1.5]], comp: true },
    laptop: { mono: false, hp: 170, lp: 14000, peaks: [[3000, 1, 1.5]] },
    earbuds: { mono: false, hp: 30, lp: 16500, shelves: [['lowshelf', 100, 2.5], ['highshelf', 7500, 2]] },
    car: { mono: false, hp: 38, lp: 10500, shelves: [['lowshelf', 90, 5]], peaks: [[2200, 0.9, -3]] },
    mono: { mono: true }
};
AudioStore.prototype.setTranslation = function (id) {
    const ctx = this.ctx, dest = ctx.destination;
    try { this.masterGain.disconnect(dest); } catch (e) { }
    (this._devNodes || []).forEach((n) => { try { n.disconnect(); } catch (e) { } });
    this._devNodes = []; this.translation = id || 'off';
    const P = DEVICE_PROFILES[id];
    if (!P) { this.masterGain.connect(dest); return; }
    let last = this.masterGain;
    const add = (n) => { last.connect(n); last = n; this._devNodes.push(n); };
    const bq = (type, f, q, g) => { const n = ctx.createBiquadFilter(); n.type = type; n.frequency.value = f; if (q != null) n.Q.value = q; if (g != null) n.gain.value = g; return n; };
    if (P.mono) { const m = ctx.createGain(); m.channelCount = 1; m.channelCountMode = 'explicit'; m.channelInterpretation = 'speakers'; add(m); }
    if (P.hp) add(bq('highpass', P.hp, 0.7));
    (P.shelves || []).forEach(([t, f, g]) => add(bq(t, f, null, g)));
    (P.peaks || []).forEach(([f, q, g]) => add(bq('peaking', f, q, g)));
    if (P.lp) add(bq('lowpass', P.lp, 0.7));
    if (P.comp) { const c = ctx.createDynamicsCompressor(); c.threshold.value = -24; c.ratio.value = 4; c.attack.value = 0.005; c.release.value = 0.15; add(c); }
    last.connect(dest);
};


// ===================== releaseengine.js =====================
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

// ===================== releaseUI.js =====================
/* =====================================================================
   Release check: "is this ready to go out?"
   ===================================================================== */

// What counts as healthy depends on where the audio is going
const RC_TYPES = {
    music: { name: 'Music', target: -14, tol: [1.5, 4], noise: [-45, -35], lra: [2, 16], maxLead: 3 },
    podcast: { name: 'Podcast', target: -16, tol: [1.5, 4], noise: [-55, -45], lra: [1.5, 12], maxLead: 2 },
    video: { name: 'Video', target: -14, tol: [1.5, 4], noise: [-55, -45], lra: [2, 15], maxLead: 2 },
    radio: { name: 'Radio', target: -23, tol: [1, 3], noise: [-55, -45], lra: [2, 15], maxLead: 2 }
};
// Normalisation targets of the main services (integrated loudness, LUFS). "down" = only ever turns loud tracks down.
const RC_PLATFORMS = [
    { name: 'Spotify', target: -14, mode: 'both' }, { name: 'Apple Music', target: -16, mode: 'both' },
    { name: 'YouTube', target: -14, mode: 'down' }, { name: 'Tidal', target: -14, mode: 'both' },
    { name: 'Amazon Music', target: -14, mode: 'both' }, { name: 'Apple Podcasts', target: -16, mode: 'both' },
    { name: 'Broadcast (EBU R128)', target: -23, mode: 'both' }
];
const RC_DEVICES = [['off', 'Original'], ['phone', 'Phone'], ['speaker', 'Bluetooth speaker'], ['laptop', 'Laptop'], ['earbuds', 'Earbuds'], ['car', 'Car'], ['mono', 'Mono']];

const rcModal = $('release-modal');
const RC = { R: null, checks: [], type: 'music', token: 0, scanning: false };

const f1 = (v) => (isFinite(v) ? v.toFixed(1) : '--');
const at = (t) => fmtTime(t, 1).replace(/^00:/, '');

// ---------- turn measurements into plain-language checks ----------
function buildChecks(R, type) {
    const T = RC_TYPES[type], rows = [], add = (r) => rows.push(r);
    const dbOf = (v) => 20 * Math.log10(v + 1e-12);

    // loudness
    if (!isFinite(R.lufs)) add({ id: 'loud', title: 'Loudness', status: 'bad', detail: 'The track is silent or far too quiet to measure.', fix: null });
    else {
        const d = R.lufs - T.target, ad = Math.abs(d);
        add({
            id: 'loud', title: 'Loudness', status: ad <= T.tol[0] ? 'ok' : ad <= T.tol[1] ? 'warn' : 'bad',
            detail: `${f1(R.lufs)} LUFS. A ${T.name.toLowerCase()} release aims for ${T.target}.` + (ad > T.tol[0] ? ` About ${f1(ad)} dB too ${d > 0 ? 'loud' : 'quiet'}.` : ''),
            fix: ad > T.tol[0] ? ['loudness'] : null, fixLabel: `Set to ${T.target}`
        });
    }
    // peaks that survive conversion to MP3 / AAC
    add({
        id: 'tp', title: 'Peak level', status: R.truePeakDb > -0.1 ? 'bad' : R.truePeakDb > -1 ? 'warn' : 'ok',
        detail: `Highest peak ${f1(R.truePeakDb)} dB.` + (R.truePeakDb > -1 ? ' Streaming services re-encode your file, and peaks this high can distort. Aim for -1 dB or lower.' : ' Safe headroom.'),
        fix: R.truePeakDb > -1 ? ['peak'] : null, fixLabel: 'Limit to -1 dB'
    });
    // clipping
    add({
        id: 'clip', title: 'Clipping', status: R.clipEvents === 0 ? 'ok' : R.clipEvents < 10 ? 'warn' : 'bad',
        detail: R.clipEvents === 0 ? 'No flat-topped (clipped) peaks.' : `${R.clipEvents} clipped moment${R.clipEvents > 1 ? 's' : ''}, first at ${at(R.clipTimes[0])}. This sounds like harsh crackle.`,
        fix: R.clipEvents ? ['clip', 'peak'] : null, fixLabel: 'Repair', locs: R.clipTimes, marker: 'Clipping'
    });
    // dynamics
    if (R.duration < 12 || !R.lra) add({ id: 'lra', title: 'Dynamics', status: 'ok', detail: R.duration < 12 ? 'Too short to judge the volume range.' : 'The volume stays very even.', fix: null });
    else add({
        id: 'lra', title: 'Dynamics', status: R.lra < T.lra[0] ? 'warn' : R.lra > T.lra[1] ? 'warn' : 'ok',
        detail: `Volume range ${f1(R.lra)} LU.` + (R.lra < T.lra[0] ? ' Very squashed, which can sound tiring.' : R.lra > T.lra[1] ? ' Big swings: quiet parts may vanish on phones or in cars.' : ' A healthy amount of movement.'), fix: null
    });
    // noise
    if (!R.hasQuietMoments) add({ id: 'noise', title: 'Background noise', status: 'ok', detail: 'No quiet passages to judge, so noise is not an issue you can hear in the gaps.', fix: null });
    else add({
        id: 'noise', title: 'Background noise', status: R.noiseFloorDb <= T.noise[0] ? 'ok' : R.noiseFloorDb <= T.noise[1] ? 'warn' : 'bad',
        detail: `Quietest moments sit at ${f1(R.noiseFloorDb)} dB.` + (R.noiseFloorDb > T.noise[0] ? ' Audible hiss or room noise.' : ' Clean.'),
        fix: R.noiseFloorDb > T.noise[0] ? ['noise'] : null, fixLabel: 'Reduce noise', safe: type !== 'music'
    });
    // hum
    add({
        id: 'hum', title: 'Mains hum', status: !R.hum.hz ? 'ok' : (dbOf(R.hum.level) > -35 && type !== 'music' ? 'bad' : 'warn'),
        detail: !R.hum.hz ? 'No electrical hum found.' : `${R.hum.hz} Hz hum${type === 'music' ? ' (possibly a bass note, check by ear)' : ''} at ${f1(dbOf(R.hum.level))} dB.`,
        fix: R.hum.hz ? ['hum'] : null, fixLabel: 'Remove hum', safe: type !== 'music'
    });
    // clicks
    add({
        id: 'clicks', title: 'Clicks and pops', status: R.clicks === 0 ? 'ok' : 'warn',
        detail: R.clicks === 0 ? 'No clicks found.' : `${R.clicks} possible click${R.clicks > 1 ? 's' : ''}, first at ${at(R.clickTimes[0])}.`,
        fix: R.clicks ? ['clicks'] : null, fixLabel: 'Remove clicks', locs: R.clickTimes, marker: 'Click', safe: type !== 'music'
    });
    // DC offset
    add({
        id: 'dc', title: 'DC offset', status: R.dc <= 0.005 ? 'ok' : R.dc <= 0.02 ? 'warn' : 'bad',
        detail: R.dc <= 0.005 ? 'Centred correctly.' : 'The waveform sits off-centre, which wastes headroom and can click at edits.', fix: R.dc > 0.005 ? ['dc'] : null, fixLabel: 'Re-centre'
    });
    // start and end
    const longLead = R.leadSilence > T.maxLead, longTrail = R.trailSilence > 6, abrupt = R.startLevel > 0.05 || R.endLevel > 0.05, notes = [];
    if (longLead) notes.push(`${f1(R.leadSilence)} s of silence at the start`);
    if (longTrail) notes.push(`${f1(R.trailSilence)} s of silence at the end`);
    if (R.startLevel > 0.05) notes.push('starts abruptly');
    if (R.endLevel > 0.05) notes.push('ends abruptly (may click)');
    add({
        id: 'ends', title: 'Start and end', status: notes.length ? 'warn' : 'ok', detail: notes.length ? notes.join(', ') + '.' : 'Clean start and a clean finish.',
        fix: notes.length ? ['ends'] : null, fixLabel: 'Tidy ends'
    });
    // stereo
    if (R.ch < 2 || R.correlation === null) add({ id: 'stereo', title: 'Stereo and mono', status: 'ok', detail: 'Mono file: it plays the same everywhere.', fix: null });
    else {
        const bad = R.correlation < -0.3 || R.monoLossDb < -6, warn = R.correlation < 0.1 || R.monoLossDb < -3;
        add({
            id: 'stereo', title: 'Stereo and mono', status: bad ? 'bad' : warn ? 'warn' : 'ok',
            detail: bad ? `The sides cancel each other (${f1(R.monoLossDb)} dB in mono). On a phone or smart speaker, parts of this will disappear.`
                : warn ? `Very wide image: you lose ${f1(-R.monoLossDb)} dB when played in mono.` : `Holds up in mono (${f1(R.monoLossDb)} dB).`,
            fix: bad || warn ? ['stereo'] : null, fixLabel: bad ? 'Make mono' : 'Narrow image', safe: false
        });
    }
    // sample rate
    add({ id: 'sr', title: 'Sample rate', status: R.sr < 44100 && type !== 'radio' ? 'warn' : 'ok', detail: `${R.sr / 1000} kHz.` + (R.sr < 44100 ? ' Below CD quality.' : ''), fix: null });
    return rows;
}

// ---------- show the results ----------
const RC_ICON = { ok: 'check', warn: 'priority_high', bad: 'close', info: 'info' };
function renderRelease() {
    const R = RC.R; if (!R) return;
    RC.checks = buildChecks(R, RC.type);
    const bad = RC.checks.filter((c) => c.status === 'bad').length, warn = RC.checks.filter((c) => c.status === 'warn').length;
    const score = Math.max(0, Math.min(100, 100 - bad * 18 - warn * 6)), T = RC_TYPES[RC.type];
    const level = bad ? 'bad' : warn ? 'warn' : 'ok';
    $('rc-ring').className = 'rc-ring ' + level;
    $('rc-ring-fg').style.strokeDashoffset = (213.6 * (1 - score / 100)).toFixed(1);
    $('rc-score').textContent = score;
    $('rc-title').textContent = bad ? 'Not ready yet' : warn ? 'Almost ready' : 'Ready to release';
    $('rc-sub').textContent = bad ? `${bad} thing${bad > 1 ? 's' : ''} should be fixed first${warn ? `, plus ${warn} to look at` : ''}.`
        : warn ? `${warn} small thing${warn > 1 ? 's' : ''} worth a look before you publish.` : `Every check passed for a ${T.name.toLowerCase()} release.`;

    const list = $('rc-list'); list.innerHTML = '';
    RC.checks.forEach((c) => {
        const li = document.createElement('li'); li.className = 'rc-row ' + c.status;
        li.innerHTML = `<span class="rc-dot"><span class="material-symbols-rounded">${RC_ICON[c.status]}</span></span>
            <div class="rc-text"><b></b><small></small></div><div class="rc-btns"></div>`;
        li.querySelector('b').textContent = c.title; li.querySelector('small').textContent = c.detail;
        const btns = li.querySelector('.rc-btns');
        if (c.locs && c.locs.length) { const b = document.createElement('button'); b.className = 'chip'; b.textContent = 'Show'; b.addEventListener('click', () => showIssue(c)); btns.appendChild(b); }
        if (c.fix) { const b = document.createElement('button'); b.className = 'chip fix'; b.textContent = c.fixLabel || 'Fix'; b.addEventListener('click', () => applyReleaseFixes(c.fix, `Fixed: ${c.title.toLowerCase()}`)); btns.appendChild(b); }
        list.appendChild(li);
    });
    const safe = RC.checks.filter((c) => c.status !== 'ok' && c.fix && c.safe !== false);
    $('rc-fixall').disabled = !safe.length;
    $('rc-fixall').textContent = safe.length ? `Fix ${safe.length} thing${safe.length > 1 ? 's' : ''} safely` : 'Nothing to fix';

    // what each service will do to this track
    const box = $('rc-platforms'); box.innerHTML = '';
    RC_PLATFORMS.forEach((p) => {
        const row = document.createElement('div'); row.className = 'rc-plat-row';
        let txt, cls = 'same';
        if (!isFinite(R.lufs)) txt = '--';
        else {
            const g = p.target - R.lufs;
            if (Math.abs(g) < 0.3) { txt = 'no change'; }
            else if (g < 0) { txt = `down ${f1(-g)} dB`; cls = 'down'; }
            else if (p.mode === 'down') { txt = 'no change'; }
            else { txt = `up ${f1(g)} dB`; cls = 'up'; }
        }
        row.innerHTML = `<span class="rc-plat-name"></span><span class="rc-plat-t"></span><span class="rc-plat-g ${cls}"></span>`;
        row.children[0].textContent = p.name; row.children[1].textContent = `${p.target}`; row.children[2].textContent = txt;
        box.appendChild(row);
    });
}

// ---------- scanning ----------
async function runReleaseScan() {
    if (!store.audioBuffer) return;
    const tk = ++RC.token; RC.scanning = true;
    $('rc-title').textContent = 'Scanning your track...'; $('rc-sub').textContent = 'Checking loudness, peaks, noise, hum and more.';
    $('rc-ring').className = 'rc-ring scanning'; $('rc-score').textContent = '...';
    $('rc-list').innerHTML = '<li class="rc-row scanning"><div class="rc-text"><b>Listening closely</b><small>This takes a few seconds on long tracks.</small></div></li>';
    $('rc-fixall').disabled = true; $('rc-rescan').disabled = true;
    await new Promise((r) => setTimeout(r, 30));
    let R;
    try { R = await store.analyzeRelease(store.audioBuffer); }
    catch (e) { console.error(e); if (tk === RC.token) { toast("The scan didn't work on this audio.", 'error'); $('rc-sub').textContent = 'The scan failed.'; } $('rc-rescan').disabled = false; return; }
    if (tk !== RC.token) return;
    RC.R = R; RC.scanning = false; $('rc-rescan').disabled = false; renderRelease();
}

function showIssue(c) {
    closeRelease();
    markers = markers.filter((m) => !m.name.startsWith('\u26a0'));
    c.locs.slice(0, 15).forEach((t) => markers.push({ t, name: `\u26a0 ${c.marker}` }));
    markers.sort((a, b) => a.t - b.t); renderMarkers();
    seekTo(Math.max(0, c.locs[0] - 1)); animateView(Math.max(0, c.locs[0] - 4), c.locs[0] + 4);
    toast(`Marked ${Math.min(15, c.locs.length)} spot${c.locs.length > 1 ? 's' : ''}. Press play to hear the first one.`);
}

// ---------- fixing ----------
async function applyReleaseFixes(keys, label) {
    releaseCleanup();
    const R = RC.R, T = RC_TYPES[RC.type], set = new Set(keys.flat());
    if (set.has('loudness')) set.delete('peak');
    let leadCut = 0;
    await withBusy('Fixing...', () => commit(label, async () => {
        await store.processRegion(null, null, async (b0) => {
            let b = b0;
            if (set.has('dc')) store.fxDC(b);
            if (set.has('clip')) store.fxDeclip(b);
            if (set.has('clicks')) store.fxDeclick(b);
            if (set.has('hum') && R.hum.hz) b = await store.fxHum(b, R.hum.hz);
            if (set.has('noise')) b = await store.fxNoiseReduce(b, { strength: 0.55, useLearned: false });
            if (set.has('ends')) {
                if (R.leadSilence > T.maxLead || R.trailSilence > 6) { const r = store.trimSilenceEnds(b); b = r.buf; leadCut = r.lead; }
                if (R.startLevel > 0.05) store.fxFadeIn(b, 0.03);
                if (R.endLevel > 0.05) store.fxFadeOut(b, 0.08);
            }
            if (set.has('stereo')) { if (R.correlation < -0.3) store.fxMono(b); else store.fxMidSide(b, { mid: 1, side: 0.55 }); }
            if (set.has('loudness')) b = await store.levelTo(b, T.target, -1);
            else if (set.has('peak')) b = await store.limitTruePeak(b, -1);
            return b;
        });
    }, { keepMarkers: true, mapTime: (t) => Math.max(0, t - leadCut) }));
    await runReleaseScan();
}
$('rc-fixall').addEventListener('click', () => {
    const rows = RC.checks.filter((c) => c.status !== 'ok' && c.fix && c.safe !== false);
    if (rows.length) applyReleaseFixes(rows.map((c) => c.fix), `Release fixes (${rows.length})`);
});

// ---------- hear it on other devices ----------
function buildDevices() {
    const box = $('rc-devices'); box.innerHTML = '';
    RC_DEVICES.forEach(([id, name]) => {
        const b = document.createElement('button'); b.className = 'chip' + (id === 'off' ? ' active' : ''); b.dataset.device = id; b.textContent = name;
        b.addEventListener('click', () => {
            abxRestore();
            store.setTranslation(id);
            box.querySelectorAll('.chip').forEach((c) => c.classList.toggle('active', c === b));
            if (!store.isPlaying) { togglePlayPause(); }
        });
        box.appendChild(b);
    });
}
buildDevices();
function syncPlayIcon() { playIcon.innerText = store.isPlaying ? 'pause' : 'play_arrow'; playPauseBtn.classList.toggle('is-playing', store.isPlaying); }
$('rc-play').addEventListener('click', () => { togglePlayPause(); });
(function rcClock() {
    requestAnimationFrame(rcClock);
    if (rcModal.hidden) return;
    $('rc-play').textContent = store.isPlaying ? 'Pause' : 'Play';
    $('rc-time').textContent = fmtTime(store.getCurrentTime(), 0).replace(/^00:/, '') + ' / ' + fmtTime(D(), 0).replace(/^00:/, '');
})();

// ---------- trust your ears: blind A/B/X test, level-matched ----------
const ABX = { state: 'idle', round: 0, rounds: 6, score: 0, hidden: 'A', now: 'A', orig: null, cur: null, gains: { A: 1, B: 1 } };
function abxProblem() {
    const o = store.originalBuffer, c = store.audioBuffer;
    if (!o || !c) return 'Import audio first.';
    if (!store.history.length) return 'Make an edit first (try Master or Polish), then compare it with your original here.';
    if (Math.abs(o.length - c.length) > 1) return 'Your edits changed the length, so the two versions cannot be lined up. Undo cuts, trims or tempo changes to compare.';
    return null;
}
function abxUse(which) {
    ABX.now = which;
    const actual = which === 'X' ? ABX.hidden : which, buf = actual === 'A' ? ABX.orig : ABX.cur, was = store.isPlaying;
    if (was) store.pause();
    store.audioBuffer = buf; store.abGain.gain.value = ABX.gains[actual];
    store.play(); syncPlayIcon(); renderAbx();
}
function abxRestore() {
    if (ABX.state !== 'running') return;
    const was = store.isPlaying; if (was) store.pause();
    store.audioBuffer = ABX.cur; store.abGain.gain.value = 1; if (was) store.play();
    ABX.state = 'idle'; syncPlayIcon(); renderAbx();
}
function abxStart() {
    const why = abxProblem(); if (why) return toast(why, 'error');
    store.setTranslation('off'); $('rc-devices').querySelectorAll('.chip').forEach((c) => c.classList.toggle('active', c.dataset.device === 'off'));
    ABX.orig = store.originalBuffer; ABX.cur = store.audioBuffer; ABX.round = 0; ABX.score = 0; ABX.state = 'running';
    const la = store.measureLoudness(ABX.orig).lufs, lb = store.measureLoudness(ABX.cur).lufs, lo = Math.min(la, lb);
    ABX.gains = isFinite(lo) ? { A: Math.pow(10, (lo - la) / 20), B: Math.pow(10, (lo - lb) / 20) } : { A: 1, B: 1 };
    ABX.hidden = Math.random() < 0.5 ? 'A' : 'B'; abxUse('A');
}
function abxAnswer(guess) {
    if (guess === ABX.hidden) ABX.score++;
    ABX.round++;
    if (ABX.round >= ABX.rounds) {
        ABX.finalHidden = ABX.hidden;
        const was = store.isPlaying; if (was) store.pause();
        store.audioBuffer = ABX.cur; store.abGain.gain.value = 1; syncPlayIcon(); ABX.state = 'done';
        renderAbx();
    } else { ABX.hidden = Math.random() < 0.5 ? 'A' : 'B'; abxUse('A'); }
}
function abxPValue(k, n) { let p = 0, c = 1; for (let i = 0; i <= n; i++) { if (i > 0) c = c * (n - i + 1) / i; if (i >= k) p += c; } return p / Math.pow(2, n); }
function renderAbx() {
    const box = $('rc-abx');
    if (ABX.state === 'idle') {
        const why = abxProblem();
        box.innerHTML = `<p>Can you really hear the difference your edits made? A blind test, with both versions at the <b>same loudness</b> so louder does not win.</p>
            ${why ? `<p class="rc-why"></p>` : ''}<button class="ghost-btn" id="abx-start" ${why ? 'disabled' : ''}>Start the blind test</button>`;
        if (why) box.querySelector('.rc-why').textContent = why;
        const b = $('abx-start'); if (b) b.addEventListener('click', abxStart);
    } else if (ABX.state === 'running') {
        box.innerHTML = `<p class="abx-round">Round ${ABX.round + 1} of ${ABX.rounds}</p>
            <div class="abx-listen">${['A', 'B', 'X'].map((k) => `<button class="chip ${ABX.now === k ? 'active' : ''}" data-l="${k}">${k === 'A' ? 'A  before' : k === 'B' ? 'B  after' : 'X  mystery'}</button>`).join('')}</div>
            <p>X is secretly A or B. Listen, then pick the one X matches.</p>
            <div class="abx-answer"><button class="solid-btn" data-a="A">X is A</button><button class="solid-btn" data-a="B">X is B</button></div>`;
        box.querySelectorAll('[data-l]').forEach((b) => b.addEventListener('click', () => abxUse(b.dataset.l)));
        box.querySelectorAll('[data-a]').forEach((b) => b.addEventListener('click', () => abxAnswer(b.dataset.a)));
    } else {
        const p = abxPValue(ABX.score, ABX.rounds), sure = p <= 0.05;
        box.innerHTML = `<p class="abx-score ${sure ? 'ok' : 'warn'}">${ABX.score} of ${ABX.rounds} right</p>
            <p>${sure ? 'You can reliably hear the difference. Your edits are doing something real.' : 'You could not reliably tell them apart, so the change is subtle (or louder was fooling you before).'}</p>
            <small>Chance of guessing this well by luck: ${(p * 100).toFixed(0)}%</small><button class="ghost-btn" id="abx-again">Try again</button>`;
        $('abx-again').addEventListener('click', () => { ABX.state = 'idle'; renderAbx(); });
    }
}

// ---------- open / close ----------
function releaseCleanup() {
    abxRestore(); if (ABX.state === 'done') ABX.state = 'idle';
    store.setTranslation('off'); store.abGain.gain.value = 1;
    $('rc-devices').querySelectorAll('.chip').forEach((c) => c.classList.toggle('active', c.dataset.device === 'off'));
}
function openRelease() {
    if (!store.audioBuffer) return toast('Import a track (or try the demo song) first.', 'error');
    if (typeof masterGuard === 'function') masterGuard();
    if (rec) return toast('Stop the recording first.', 'error');
    ABX.state = 'idle'; rcModal.hidden = false; renderAbx(); runReleaseScan();
}
function closeRelease() {
    if (rcModal.hidden) return;
    RC.token++; releaseCleanup();
    if (store.isPlaying) { store.pause(); }
    syncPlayIcon(); rcModal.hidden = true;
}
$('release-btn').addEventListener('click', openRelease);
$('rc-close').addEventListener('click', closeRelease);
$('rc-done').addEventListener('click', closeRelease);
$('rc-rescan').addEventListener('click', () => { releaseCleanup(); runReleaseScan(); });
rcModal.addEventListener('mousedown', (e) => { if (e.target === rcModal) closeRelease(); });
document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && !rcModal.hidden) { e.stopPropagation(); closeRelease(); } }, true);
document.querySelectorAll('#rc-type .seg').forEach((b) => b.addEventListener('click', () => {
    RC.type = b.dataset.type; document.querySelectorAll('#rc-type .seg').forEach((x) => x.classList.toggle('active', x === b)); renderRelease();
}));

const _extra4 = extraCommands;
extraCommands = function () { return [{ name: 'Release check: is it ready?', icon: 'verified', hint: 'Check', run: openRelease }, ..._extra4()]; };

// ===================== lyrics.js =====================
/* =====================================================================
   Lyrics and subtitles: synced to the beat, the vocals and the playback speed
   Times are song times (seconds into the audio), so they stay correct at any playback speed.
   ===================================================================== */

let subs = [];              // [{ text, start }]  start is null until a line has been timed
let subsShow = true, tapMode = false, snapStep = 1, beatGrid = null, tapStack = [];
const TAP_LATENCY = 0.06;   // people tap a little after they hear the line begin
const lyList = $('ly-list'), subStrip = $('sub-strip'), subOverlay = $('sub-overlay'), subCur = $('sub-cur'), subNext = $('sub-next'), beatCanvas = $('beat-canvas');

// ---------- helpers ----------
function sortSubs() {
    const timed = subs.filter((s) => s.start != null).sort((a, b) => a.start - b.start), untimed = subs.filter((s) => s.start == null);
    subs = [...timed, ...untimed];
}
function subEnd(i) { // a line lasts until the next one starts (and never longer than 8 seconds)
    const s = subs[i]; if (s.start == null) return null;
    let e = null; for (let j = i + 1; j < subs.length; j++) if (subs[j].start != null) { e = subs[j].start - 0.04; break; }
    if (e == null) e = Math.min(D() || s.start + 6, s.start + 6);
    return Math.max(Math.min(e, s.start + 8), s.start + 0.3);
}
const lyFmt = (t) => `${Math.floor(t / 60)}:${(t % 60).toFixed(2).padStart(5, '0')}`;
function lyParseTime(str) {
    str = String(str).trim(); if (!str) return null;
    const m = str.match(/^(?:(\d+):)?(\d+(?:\.\d+)?)$/); if (!m) return null;
    return (m[1] ? +m[1] * 60 : 0) + +m[2];
}
function subsSnapshot() { return subs.map((s) => ({ ...s })); }
function subsRestore(arr) { subs = (arr || []).map((s) => ({ ...s })); lyRender(); scheduleDraw(); }
function afterSubsChange() { sortSubs(); lyRender(); scheduleDraw(); }

// ---------- reading lyric files: LRC, SRT, VTT or plain text ----------
function parseLyrics(text) {
    const clean = text.replace(/\r/g, ''), out = [];
    if (/-->/.test(clean)) {
        clean.split(/\n\s*\n/).forEach((block) => {
            const lines = block.split('\n').map((l) => l.trim()).filter(Boolean), i = lines.findIndex((l) => l.includes('-->')); if (i < 0) return;
            const m = lines[i].match(/(?:(\d+):)?(\d{1,2}):(\d{2})[.,](\d{1,3})/); if (!m) return;
            const start = (m[1] ? +m[1] * 3600 : 0) + +m[2] * 60 + +m[3] + +('0.' + m[4]);
            const txt = lines.slice(i + 1).join(' ').replace(/<[^>]+>/g, '').trim(); if (txt) out.push({ text: txt, start });
        });
        return out;
    }
    const rows = clean.split('\n'), lrc = /^\s*((?:\[\d{1,3}:\d{2}(?:[.:]\d{1,3})?\]\s*)+)(.*)$/; let timed = false;
    rows.forEach((line) => {
        const m = lrc.exec(line); if (!m) return;
        timed = true; const txt = m[2].trim(); if (!txt) return;
        [...m[1].matchAll(/\[(\d{1,3}):(\d{2})(?:[.:](\d{1,3}))?\]/g)].forEach((t) => out.push({ text: txt, start: +t[1] * 60 + +t[2] + (t[3] ? +('0.' + t[3]) : 0) }));
    });
    if (timed) return out.sort((a, b) => a.start - b.start);
    return rows.map((l) => l.trim()).filter(Boolean).map((text) => ({ text, start: null }));
}

// ---------- the beat grid ----------
function gridStatus() {
    const b = $('ly-grid-status');
    b.textContent = beatGrid ? `${beatGrid.bpm.toFixed(1)} BPM` : 'No beat grid yet'; b.classList.toggle('on', !!beatGrid);
}
async function ensureGrid() {
    if (!store.audioBuffer) return null;
    if (beatGrid && beatGrid.len === store.audioBuffer.length) return beatGrid;
    const g = await store.detectBeats(store.audioBuffer);
    beatGrid = g ? { ...g, len: store.audioBuffer.length } : null;
    gridStatus(); scheduleDraw();
    return beatGrid;
}
function lySnap(t) {
    if (!snapStep || !beatGrid) return t;
    const step = beatGrid.period * snapStep, n = Math.round((t - beatGrid.offset) / step);
    return Math.max(0, beatGrid.offset + n * step);
}
function drawBeatGrid() {
    const g = beatCanvas.getContext('2d');
    if (activeTab !== 'lyrics' || !beatGrid || !store.audioBuffer || waveStyle === 'spectro') { if (beatCanvas.width) g.clearRect(0, 0, beatCanvas.width, beatCanvas.height); return; }
    const dpr = window.devicePixelRatio || 1, w = container.clientWidth, h = container.clientHeight; if (w <= 0) return;
    sizeCanvas(beatCanvas, w, h, dpr);
    const W = beatCanvas.width, H = beatCanvas.height; g.clearRect(0, 0, W, H);
    const px = (beatGrid.period / span()) * W; // pixels between beats
    const n0 = Math.ceil((view.start - beatGrid.offset) / beatGrid.period), n1 = Math.floor((view.end - beatGrid.offset) / beatGrid.period);
    for (let n = Math.max(0, n0); n <= n1; n++) {
        const bar = n % 4 === 0; if (px < 5 * dpr && !bar) continue; if (px * 4 < 5 * dpr) break;
        const x = Math.round(frac(beatGrid.offset + n * beatGrid.period) * W) + 0.5;
        g.strokeStyle = bar ? `rgba(${TC.rgb_amber},0.5)` : `rgba(${TC.rgb_amber},0.18)`; g.lineWidth = (bar ? 1.5 : 1) * dpr;
        g.beginPath(); g.moveTo(x, 22 * dpr); g.lineTo(x, H); g.stroke();
    }
}

// ---------- the list of lines ----------
function lyCount() {
    const un = subs.filter((s) => s.start == null).length;
    $('ly-count').textContent = `${subs.length} line${subs.length === 1 ? '' : 's'}` + (un ? `, ${un} to time` : '');
}
function lyRender() {
    lyList.innerHTML = '';
    const nextUntimed = subs.findIndex((s) => s.start == null);
    subs.forEach((s, i) => {
        const li = document.createElement('li');
        li.className = 'ly-item' + (s.start == null ? ' untimed' : '') + (tapMode && i === nextUntimed ? ' is-next' : '');
        li.innerHTML = `<button class="ly-go" title="Jump to this line"><span class="material-symbols-rounded">play_arrow</span></button>
            <input class="ly-time" aria-label="Start time" placeholder="--:--">
            <input class="ly-input" aria-label="Line text">
            <button class="ly-now" title="Set this line to start at the playhead"><span class="material-symbols-rounded">schedule</span></button>
            <button class="ly-del" title="Delete this line"><span class="material-symbols-rounded">close</span></button>`;
        const time = li.querySelector('.ly-time'), text = li.querySelector('.ly-input');
        time.value = s.start == null ? '' : lyFmt(s.start); text.value = s.text;
        li.querySelector('.ly-go').addEventListener('click', () => { if (s.start != null) seekTo(s.start); });
        time.addEventListener('change', () => { s.start = lyParseTime(time.value); afterSubsChange(); });
        text.addEventListener('input', () => { s.text = text.value; });
        li.querySelector('.ly-now').addEventListener('click', () => { s.start = lySnap(store.getCurrentTime()); afterSubsChange(); });
        li.querySelector('.ly-del').addEventListener('click', () => { subs.splice(subs.indexOf(s), 1); afterSubsChange(); });
        lyList.appendChild(li);
    });
    lyCount();
}

// ---------- subtitles on the waveform ----------
function renderSubs() {
    subStrip.innerHTML = '';
    if (!subsShow || !store.audioBuffer) return;
    subs.forEach((s, i) => {
        if (s.start == null) return;
        const e = subEnd(i), a = frac(s.start), b = frac(e); if (b < 0 || a > 1) return;
        const el = document.createElement('div'); el.className = 'sub-block'; el.dataset.i = i; el.title = s.text;
        el.style.left = (Math.max(0, a) * 100) + '%'; el.style.width = Math.max(0.3, (Math.min(1, b) - Math.max(0, a)) * 100) + '%';
        el.textContent = s.text; el.addEventListener('click', () => seekTo(s.start));
        subStrip.appendChild(el);
    });
}
let lastCur = -2, lastNext = -2;
(function subTick() {
    requestAnimationFrame(subTick);
    if (!subs.length || !store.audioBuffer) { subOverlay.hidden = true; return; }
    const t = store.getCurrentTime();
    let idx = -1; for (let i = 0; i < subs.length; i++) { if (subs[i].start != null && subs[i].start <= t + 0.001) idx = i; else if (subs[i].start != null) break; }
    const live = idx >= 0 && t < subEnd(idx);
    let nxt = -1; for (let i = idx + 1; i < subs.length; i++) if (subs[i].start != null) { nxt = i; break; }
    if (idx < 0) { for (let i = 0; i < subs.length; i++) if (subs[i].start != null) { nxt = i; break; } }
    subOverlay.hidden = !subsShow || (!live && nxt < 0);
    const curI = live ? idx : -1;
    if (curI !== lastCur) { subCur.textContent = curI >= 0 ? subs[curI].text : ''; lastCur = curI; }
    if (nxt !== lastNext) { subNext.textContent = nxt >= 0 ? subs[nxt].text : ''; lastNext = nxt; }
    subCur.style.setProperty('--p', curI >= 0 ? clamp((t - subs[curI].start) / (subEnd(curI) - subs[curI].start), 0, 1) * 100 + '%' : '0%');
    subCur.classList.toggle('empty', curI < 0);
    // highlight in the list and on the strip
    if (activeTab === 'lyrics' || subStrip.childNodes.length) {
        lyList.querySelectorAll('.ly-item').forEach((el, i) => el.classList.toggle('is-now', i === curI));
        subStrip.querySelectorAll('.sub-block').forEach((el) => el.classList.toggle('on', +el.dataset.i === curI));
    }
})();

// ---------- tap to sync ----------
function tapBar() { $('ly-tapbar').hidden = !tapMode; $('ly-tap').classList.toggle('active', tapMode); lyRender(); }
function startTap() {
    if (!store.audioBuffer) return toast('Import a song first.', 'error');
    if (!subs.some((s) => s.start == null)) return toast('Every line already has a time. Clear one first, or paste new lyrics.', 'error');
    tapMode = true; tapStack = []; tapBar();
    if (!store.isPlaying) togglePlayPause();
    toast('Press T (or Tap now) the moment each line begins.');
}
function endTap(done) { tapMode = false; tapBar(); if (done) toast('All lines timed. Play it back to check, or fine-tune any time.'); }
function tapNext() {
    const idx = subs.findIndex((s) => s.start == null); if (idx < 0) return endTap(true);
    let t = lySnap(Math.max(0, store.getCurrentTime() - TAP_LATENCY));
    let prev = -1; for (let i = 0; i < idx; i++) if (subs[i].start != null) prev = Math.max(prev, subs[i].start);
    if (t <= prev) t = prev + 0.05;
    subs[idx].start = t; tapStack.push(idx); lyRender(); scheduleDraw();
    const li = lyList.children[idx]; if (li) li.scrollIntoView({ block: 'nearest' });
    if (!subs.some((s) => s.start == null)) endTap(true);
}
function undoTap() {
    const i = tapStack.pop(); if (i == null) return toast('Nothing to undo.', 'error');
    subs[i].start = null; lyRender(); scheduleDraw();
}
$('ly-tap').addEventListener('click', () => (tapMode ? endTap(false) : startTap()));
$('ly-tap-now').addEventListener('click', tapNext);
$('ly-tap-undo').addEventListener('click', undoTap);
$('ly-tap-done').addEventListener('click', () => endTap(false));

// ---------- automatic placement ----------
async function spreadOnBeat() {
    if (!subs.length) return toast('Add some lyrics first.', 'error');
    const grid = await withBusy('Finding the beat...', ensureGrid);
    if (!grid) return toast('No steady beat found in this song. Try "Fit to vocals", or tap to sync.', 'error');
    const phr = store.findPhrases(store.audioBuffer), startAt = phr.length ? phr[0][0] : 0;
    const first = grid.offset + Math.max(0, Math.ceil((startAt - grid.offset) / grid.period - 0.001)) * grid.period;
    const avail = D() - first - 1;
    const per = [16, 8, 4, 2, 1].find((k) => subs.length * k * grid.period <= avail);
    if (per) subs.forEach((s, i) => { s.start = first + i * per * grid.period; });
    else { const step = Math.max(1, Math.floor(avail / grid.period / subs.length)) * grid.period; subs.forEach((s, i) => { s.start = Math.min(D() - 0.5, first + i * step); }); }
    afterSubsChange(); toast(`Placed ${subs.length} lines on the beat${per ? `, ${per} beat${per > 1 ? 's' : ''} each` : ''}.`);
}
function fitToVocals() {
    if (!subs.length) return toast('Add some lyrics first.', 'error');
    const phr = store.findPhrases(store.audioBuffer); if (!phr.length) return toast('No singing or speaking found to fit to.', 'error');
    const total = phr.reduce((a, [s, e]) => a + (e - s), 0), L = subs.length;
    subs.forEach((ln, i) => {
        let pos = (i / L) * total, k = 0; while (k < phr.length - 1 && pos >= phr[k][1] - phr[k][0]) { pos -= phr[k][1] - phr[k][0]; k++; }
        ln.start = lySnap(phr[k][0] + (pos < 0.35 ? 0 : pos));
    });
    afterSubsChange(); toast(`Fitted ${L} lines to ${phr.length} vocal phrase${phr.length > 1 ? 's' : ''}.`);
}
async function snapAll() {
    const grid = await withBusy('Finding the beat...', ensureGrid);
    if (!grid) return toast('No steady beat found, so there is nothing to snap to.', 'error');
    const keep = snapStep; if (!snapStep) snapStep = 1;
    subs.forEach((s) => { if (s.start != null) s.start = lySnap(s.start); });
    snapStep = keep; afterSubsChange(); toast('Every line now starts exactly on the beat.');
}
$('ly-beats').addEventListener('click', spreadOnBeat);
$('ly-phrases').addEventListener('click', fitToVocals);
$('ly-snap-all').addEventListener('click', snapAll);

// ---------- loading, editing, nudging ----------
$('ly-load').addEventListener('click', () => {
    const txt = $('ly-text').value; if (!txt.trim()) return toast('Paste some lyrics first.', 'error');
    subs = parseLyrics(txt); afterSubsChange();
    toast(`${subs.length} line${subs.length === 1 ? '' : 's'} ready.` + (subs.some((s) => s.start == null) ? ' Now sync them to the music.' : ''));
});
$('ly-open').addEventListener('click', () => $('ly-file').click());
$('ly-file').addEventListener('change', async (e) => {
    const f = e.target.files[0]; if (!f) return;
    subs = parseLyrics(await f.text()); afterSubsChange();
    $('ly-text').value = subs.map((s) => s.text).join('\n'); e.target.value = '';
    toast(`Opened ${f.name}: ${subs.length} lines.`);
});
$('ly-add').addEventListener('click', () => {
    subs.push({ text: 'New line', start: store.audioBuffer ? lySnap(store.getCurrentTime()) : null }); afterSubsChange();
    const li = lyList.lastElementChild; if (li) { li.scrollIntoView({ block: 'nearest' }); li.querySelector('.ly-input').select(); }
});
$('ly-show').addEventListener('change', (e) => { subsShow = e.target.checked; scheduleDraw(); });
document.querySelectorAll('#ly-snap .seg').forEach((b) => b.addEventListener('click', () => {
    snapStep = +b.dataset.snap; document.querySelectorAll('#ly-snap .seg').forEach((x) => x.classList.toggle('active', x === b));
    if (snapStep && !beatGrid) ensureGrid();
}));
document.querySelectorAll('[data-nudge]').forEach((b) => b.addEventListener('click', () => {
    const d = +b.dataset.nudge; if (!subs.some((s) => s.start != null)) return toast('No timed lines to shift yet.', 'error');
    subs.forEach((s) => { if (s.start != null) s.start = Math.max(0, s.start + d); }); afterSubsChange();
}));

// ---------- speed: subtitles keep their place at any playback speed ----------
function lySetSpeed(r, quiet) {
    store.setRate(r); $('speed-btn').textContent = r + '\u00d7'; $('speed-btn').classList.toggle('on', r !== 1);
    document.querySelectorAll('#ly-speeds .chip').forEach((c) => c.classList.toggle('active', +c.dataset.rate === r));
    if (!quiet) toast(r === 1 ? 'Normal speed.' : `Playing at ${r}x. The pitch follows the speed, and the subtitles stay in time.`);
}
const LY_RATES = [0.5, 0.75, 1, 1.25, 1.5];
$('speed-btn').addEventListener('click', () => lySetSpeed(LY_RATES[(LY_RATES.indexOf(store.rate) + 1) % LY_RATES.length]));
document.querySelectorAll('#ly-speeds .chip').forEach((c) => c.addEventListener('click', () => lySetSpeed(+c.dataset.rate)));
$('ly-retime').addEventListener('click', () => {
    const v = +$('ly-newspeed').value; if (!(v >= 25 && v <= 400) || v === 100) return toast('Enter the song\'s new speed as a percentage, like 110.', 'error');
    subs.forEach((s) => { if (s.start != null) s.start = s.start / (v / 100); }); $('ly-newspeed').value = 100; afterSubsChange();
    toast(`Retimed every line for ${v}% speed.`);
});
// called by the editor whenever the song's length changes (tempo change, cut, paste, ...)
function mapSubs(opts) {
    if (!subs.length || !opts.mapTime) return;
    if (opts.tempo && !$('ly-follow').checked) return;
    subs = subs.map((s) => { if (s.start == null) return s; const t = opts.mapTime(s.start); return t == null ? null : { ...s, start: t }; })
        .filter((s) => s && (s.start == null || s.start <= D() + 0.5));
    beatGrid = null; gridStatus(); lyRender();
}

// ---------- saving ----------
function lyTimes() { return subs.map((s, i) => ({ text: s.text, start: s.start, end: s.start == null ? null : subEnd(i) })).filter((s) => s.start != null); }
const pad = (n, w = 2) => String(n).padStart(w, '0');
function stamp(t, comma) { const T = Math.round(t * 1000), h = Math.floor(T / 3600000), m = Math.floor(T % 3600000 / 60000), s = Math.floor(T % 60000 / 1000), ms = T % 1000; return `${pad(h)}:${pad(m)}:${pad(s)}${comma ? ',' : '.'}${pad(ms, 3)}`; }
function lyExport(fmt) {
    const L = lyTimes(); if (!L.length) return toast('Time at least one line first.', 'error');
    let out = '';
    if (fmt === 'srt') out = L.map((l, i) => `${i + 1}\n${stamp(l.start, true)} --> ${stamp(l.end, true)}\n${l.text}\n`).join('\n');
    else if (fmt === 'vtt') out = 'WEBVTT\n\n' + L.map((l) => `${stamp(l.start)} --> ${stamp(l.end)}\n${l.text}\n`).join('\n');
    else out = L.map((l) => { const cs = Math.round(l.start * 100); return `[${pad(Math.floor(cs / 6000))}:${pad(Math.floor(cs % 6000 / 100))}.${pad(cs % 100)}]${l.text}`; }).join('\n') + '\n';
    download(new Blob([out], { type: 'text/plain' }), `${$('project-name-text').innerText}.${fmt}`);
    toast(`Saved ${L.length} lines as .${fmt.toUpperCase()}`);
}
document.querySelectorAll('[data-fmt]').forEach((b) => b.addEventListener('click', () => lyExport(b.dataset.fmt)));

// ---------- keyboard, hooks, palette ----------
document.addEventListener('keydown', (e) => {
    const typing = (e.target.tagName === 'INPUT' && e.target.type !== 'range' && e.target.type !== 'checkbox') || e.target.tagName === 'TEXTAREA' || e.target.tagName === 'SELECT';
    if (typing || e.metaKey || e.ctrlKey || document.querySelector('.modal:not([hidden])')) return;
    if (e.key.toLowerCase() === 't') {
        e.preventDefault();
        if (e.shiftKey) { if (tapMode) undoTap(); }
        else if (tapMode) tapNext();
        else if (activeTab === 'lyrics' && subs.some((s) => s.start == null)) startTap();
    }
});
const _ofl = onFileLoaded;
onFileLoaded = function (f) { _ofl(f); subs = []; beatGrid = null; tapMode = false; tapBar(); gridStatus(); lyRender(); lySetSpeed(1, true); };
const _obc = onBufferChanged;
onBufferChanged = function () { _obc(); if (beatGrid && store.audioBuffer && beatGrid.len !== store.audioBuffer.length) { beatGrid = null; gridStatus(); } };
const _otc = onTabChanged;
onTabChanged = function (name) { _otc(name); if (name === 'lyrics') { ensureGrid(); } scheduleDraw(); };

const _extra5 = extraCommands;
extraCommands = function () {
    return [
        { name: 'Lyrics and subtitles', icon: 'subtitles', hint: 'Panel', run: () => setTab('lyrics') },
        { name: 'Tap lyrics to the beat', icon: 'touch_app', hint: 'T', run: () => { setTab('lyrics'); startTap(); } },
        { name: 'Playback speed: next', icon: 'speed', hint: 'Speed', run: () => $('speed-btn').click() },
        ..._extra5()
    ];
};
lyRender(); gridStatus();

window.__chronosReady = true; // must stay the last line: it tells the page everything above started