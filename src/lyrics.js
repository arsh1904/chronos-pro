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