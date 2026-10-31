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