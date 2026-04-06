/**
 * DEEP LABYRINTH 3D — v4 "NIGHTMARE EDITION"
 * ─────────────────────────────────────────────
 * + Variable mission objectives per level
 * + Advanced enemy AI (node patrol / ambush / trajectory prediction)
 * + Fear Director (tension regulator)
 * + Sanity system with distortion effects
 * + Dynamic horror events (false alarms, flickers, whispers)
 * + Story screens between levels
 * + Ghost apparitions (non-lethal false enemies)
 * + Enhanced audio (monster death, whispers, contextual audio)
 * + Camera follows mouse ONLY (WASD/arrows = strafe/move only)
 * + Lantern aligned to camera, recharges when off
 * + Smooth volumetric fog (no pixelation)
 * + No time limit (removed)
 * + Battery recharges slowly when off
 */

// ═══════════════════════════════════════════
// 0. CANVAS
// ═══════════════════════════════════════════
const canvas = document.getElementById('canvas3D');
const ctx = canvas.getContext('2d');
ctx.imageSmoothingEnabled = false;

// ═══════════════════════════════════════════
// 1. CONFIG
// ═══════════════════════════════════════════
const TILE  = 64;
const TEXSZ = 128;
const MAPSZ = 55;
const FOV   = Math.PI / 2.6;
const NRAYS = 360;

const WALL  = 1;
const FLOOR = 0;
const DOOR  = 2;
const KEY   = 3;
const SWITCH_TILE = 4; // new: switch/lever tile

const settings = {
    mouseSens:  0.0022,
    joyXSens:   1.0,
    joyYSens:   1.0,
    keys: { lantern:'KeyE', sprint:'ShiftLeft', pickup:'KeyF' }
};

const isMobile = /Android|iPhone|iPad|iPod|Touch/i.test(navigator.userAgent) ||
                 (navigator.maxTouchPoints > 1);

// ═══════════════════════════════════════════
// 2. STATE
// ═══════════════════════════════════════════
let map          = [];
let isRunning    = false;
let isPaused     = false;
let isDying      = false;
let deathTimer   = 0;
let level        = 1;
let score        = 0;
let lastTime     = 0;
let dangerLevel  = 0;
let dangerFlicker= 0;
let shakeX = 0, shakeY = 0;
let bobPhase     = 0;
let bobOffset    = 0;
let zBuffer      = new Float32Array(NRAYS);
let keyItems     = [];
let switchItems  = []; // for switch objective
let doorPos      = null;
let doorWallSide = null;
let gameTime     = 0;

let mapRooms      = [];
let lampSources   = [];
let cameraPitch   = 0;

const CEILING_HEIGHT_FACTOR = 0.75; // lower wall projection => higher perceived ceiling
const MAX_PITCH = 0.46;

// ── Objective system ──
let currentObjective = null; // { type, required, done, label }
let objectiveDone    = false;
let surviveChaseSecs = 0;    // for 'survive' mission

// ── Sanity ──
const sanity = {
    value: 100,       // 0-100
    rate: -0.8,       // drain per second in darkness near enemy
    regenRate: 3.5,   // regen per second away safe
    distortion: 0,    // 0-1 visual distortion
};

// ── Fear Director ──
const fearDirector = {
    tension: 0,       // 0-100
    eventCooldown: 0,
    lastJumpscareAt: -999,
    silenceActive: false,
    silenceTimer: 0,
};

// ── Horror events ──
let horrorEvents = [];      // { type, timer, data }
let whisperTimer = 0;
let whisperScheduled = false;

// ── Ghost apparitions ──
let ghosts = [];  // { x,y,angle,timer,opacity }

// ── Story screen ──
let storyScreenActive = false;

const inventory  = { keys: 0 };

const lantern = {
    on: false,
    battery: 100,
    drainRate: 1.4,
    rechargeRate: 4.0, // per second when off
};

const SPEED_WALK = 2.6;
const SPEED_RUN  = 5.0;

let stepTimer       = 0;
let breathTimer     = 0;
let heartbeatTimer  = 0;

const breathState = {
    max: 6.5,
    value: 6.5,
    recover: 2.1,
    drain: 1.4,
    holding: false,
    forcedExhale: false,
};

// ── Camera angle independent of movement ──
let cameraAngle = 0; // camera yaw (mouse only)

// ═══════════════════════════════════════════
// 3. ENTITIES
// ═══════════════════════════════════════════
const player = {
    x:0, y:0,
    speed:0, accel:0.28, decel:0.24,
    maxSpeed: SPEED_WALK,
    moveAngle: 0, // movement direction (WASD strafe)
};

const enemy = {
    x:0, y:0,
    speed: 0,
    active: false,
    state: 'patrol',
    faceAngle: 0,
    alertTimer: 0,
    searchTimer: 0,
    lastSeenX: 0, lastSeenY: 0,
    hearingRadius: 320,
    baseHearingRadius: 320,
    visionRadius: 640,
    visionAngle: Math.PI * 0.72,
    walkPhase: 0,
    // ── Advanced AI ──
    patrolNodes: [],
    patrolIdx: 0,
    ambushNode: null,
    ambushArmed: false,
    predictX: 0, predictY: 0,
    chaseTimer: 0,
    chargeTimer: 0,
    lastPlayerAngle: 0,
};

// ═══════════════════════════════════════════
// 4. AUDIO ENGINE
// ═══════════════════════════════════════════
let audioCtx = null;
function ensureAudio(){
    if(!audioCtx) audioCtx = new (window.AudioContext||window.webkitAudioContext)();
    if(audioCtx.state==='suspended') audioCtx.resume();
}
function noise(sec){
    const n = audioCtx.sampleRate*sec;
    const b = audioCtx.createBuffer(1,n,audioCtx.sampleRate);
    const d = b.getChannelData(0);
    for(let i=0;i<n;i++) d[i]=Math.random()*2-1;
    return b;
}


const assetBank = {
    textures: {
        wall: null,
        blood: null,
    },
    sounds: {
        step: null,
        exhale: null,
        growl: null,
    },
};

function loadImageAsset(url){
    const img = new Image();
    img.crossOrigin = 'anonymous';
    img.src = url;
    return img;
}

function loadAudioAsset(url){
    const a = new Audio(url);
    a.preload = 'auto';
    a.crossOrigin = 'anonymous';
    return a;
}

function playSample(sample, volume=0.5, rate=1){
    if(!sample) return false;
    const clip = sample.cloneNode(true);
    clip.volume = volume;
    clip.playbackRate = rate;
    clip.play().catch(()=>{});
    return true;
}

function preloadRealismAssets(){
    // src/url-based assets with graceful fallback to procedural rendering/synthesis.
    assetBank.textures.wall = loadImageAsset('https://images.unsplash.com/photo-1618221469555-7f3ad97540d6?auto=format&fit=crop&w=512&q=80');
    assetBank.textures.blood = loadImageAsset('https://images.unsplash.com/photo-1545239351-1141bd82e8a6?auto=format&fit=crop&w=512&q=80');

    assetBank.sounds.step = loadAudioAsset('https://cdn.pixabay.com/download/audio/2021/08/04/audio_c839919df2.mp3?filename=footstep-on-concrete-6327.mp3');
    assetBank.sounds.exhale = loadAudioAsset('https://cdn.pixabay.com/download/audio/2022/03/22/audio_eca987c6d7.mp3?filename=heavy-breathing-6165.mp3');
    assetBank.sounds.growl = loadAudioAsset('https://cdn.pixabay.com/download/audio/2022/03/15/audio_a0f9ea6b0f.mp3?filename=monster-growl-6054.mp3');
}

function playStep(run){
    if(playSample(assetBank.sounds.step, run?0.34:0.24, run?1.1:0.9)) return;
    if(!audioCtx) return;
    const t=audioCtx.currentTime;
    const o=audioCtx.createOscillator(), g=audioCtx.createGain();
    o.connect(g); g.connect(audioCtx.destination);
    o.type='sine'; o.frequency.setValueAtTime(run?88:72,t);
    o.frequency.exponentialRampToValueAtTime(28,t+0.13);
    g.gain.setValueAtTime(run?0.2:0.14,t);
    g.gain.exponentialRampToValueAtTime(0.001,t+0.15);
    o.start(t); o.stop(t+0.16);
    const ns=audioCtx.createBufferSource(), nf=audioCtx.createBiquadFilter(), ng2=audioCtx.createGain();
    ns.buffer=noise(0.06); nf.type='lowpass'; nf.frequency.value=220;
    ns.connect(nf); nf.connect(ng2); ng2.connect(audioCtx.destination);
    ng2.gain.setValueAtTime(run?0.16:0.08,t);
    ng2.gain.exponentialRampToValueAtTime(0.001,t+0.1);
    ns.start(t); ns.stop(t+0.1);
}

function playBreath(v){
    if(!audioCtx||v<0.28) return;
    const t=audioCtx.currentTime;
    const ns=audioCtx.createBufferSource(), nf=audioCtx.createBiquadFilter(), ng=audioCtx.createGain();
    ns.buffer=noise(0.4); nf.type='bandpass'; nf.frequency.value=780; nf.Q.value=1.4;
    ns.connect(nf); nf.connect(ng); ng.connect(audioCtx.destination);
    ng.gain.setValueAtTime(0,t);
    ng.gain.linearRampToValueAtTime(v*0.11,t+0.1);
    ng.gain.exponentialRampToValueAtTime(0.001,t+0.42);
    ns.start(t); ns.stop(t+0.45);
}

function playHeartbeat(v){
    if(!audioCtx||v<0.45) return;
    const t=audioCtx.currentTime;
    const o=audioCtx.createOscillator(), g=audioCtx.createGain();
    o.connect(g); g.connect(audioCtx.destination);
    o.type='sine'; o.frequency.setValueAtTime(50,t);
    o.frequency.exponentialRampToValueAtTime(25,t+0.2);
    g.gain.setValueAtTime(v*0.3,t);
    g.gain.exponentialRampToValueAtTime(0.001,t+0.24);
    o.start(t); o.stop(t+0.26);
}

function playPickup(){
    if(!audioCtx) return;
    const t=audioCtx.currentTime;
    [523,659,784].forEach((f,i)=>{
        const o=audioCtx.createOscillator(), g=audioCtx.createGain();
        o.connect(g); g.connect(audioCtx.destination);
        o.type='triangle'; o.frequency.value=f;
        const s=t+i*0.09;
        g.gain.setValueAtTime(0.16,s); g.gain.exponentialRampToValueAtTime(0.001,s+0.28);
        o.start(s); o.stop(s+0.3);
    });
}

function playDoorOpen(){
    if(!audioCtx) return;
    const t=audioCtx.currentTime;
    const o=audioCtx.createOscillator(), g=audioCtx.createGain();
    o.connect(g); g.connect(audioCtx.destination);
    o.type='sawtooth'; o.frequency.setValueAtTime(220,t);
    o.frequency.exponentialRampToValueAtTime(880,t+0.5);
    g.gain.setValueAtTime(0.22,t); g.gain.exponentialRampToValueAtTime(0.001,t+0.65);
    o.start(t); o.stop(t+0.7);
}

// Enhanced death sound — monstrous roar
function playDeathSound(){
    if(!audioCtx) return;
    const t=audioCtx.currentTime;

    // Deep creature ROAR — layered oscillators
    [28, 41, 55, 71].forEach((freq, i) => {
        const o=audioCtx.createOscillator(), g=audioCtx.createGain();
        const dist=audioCtx.createWaveShaper();
        // Distortion curve
        const curve=new Float32Array(256);
        for(let j=0;j<256;j++){
            const x=j*2/255-1;
            curve[j]=x<0 ? -Math.pow(-x,0.6)*1.8 : Math.pow(x,0.6)*1.8;
        }
        dist.curve=curve;
        o.connect(dist); dist.connect(g); g.connect(audioCtx.destination);
        o.type='sawtooth';
        o.frequency.setValueAtTime(freq*(1+Math.random()*0.05),t+i*0.04);
        o.frequency.setValueAtTime(freq*0.5,t+0.3);
        o.frequency.exponentialRampToValueAtTime(freq*0.15,t+2.2);
        g.gain.setValueAtTime(0,t+i*0.04);
        g.gain.linearRampToValueAtTime(0.18-i*0.02,t+i*0.04+0.1);
        g.gain.exponentialRampToValueAtTime(0.001,t+2.5);
        o.start(t+i*0.04); o.stop(t+2.6);
    });

    // Wet, heavy breath exhale
    const ns=audioCtx.createBufferSource(), nf=audioCtx.createBiquadFilter(), ng=audioCtx.createGain();
    ns.buffer=noise(2.5); nf.type='bandpass'; nf.frequency.value=180; nf.Q.value=0.8;
    ns.connect(nf); nf.connect(ng); ng.connect(audioCtx.destination);
    ng.gain.setValueAtTime(0.55,t+0.05);
    ng.gain.setValueAtTime(0.7,t+0.3);
    ng.gain.exponentialRampToValueAtTime(0.001,t+2.4);
    ns.start(t); ns.stop(t+2.5);

    // Screech overtone
    const os=audioCtx.createOscillator(), gs=audioCtx.createGain();
    os.connect(gs); gs.connect(audioCtx.destination);
    os.type='sawtooth'; os.frequency.setValueAtTime(680,t+0.05);
    os.frequency.exponentialRampToValueAtTime(45,t+1.5);
    gs.gain.setValueAtTime(0.22,t+0.05);
    gs.gain.exponentialRampToValueAtTime(0.001,t+1.6);
    os.start(t+0.05); os.stop(t+1.7);
}

// Terrifying enemy approach sound
function playEnemyGrowl(intensity){
    if(intensity>=0.3&&playSample(assetBank.sounds.growl, Math.min(0.8,0.35+intensity*0.3), 0.8+intensity*0.35)) return;
    if(!audioCtx||intensity<0.3) return;
    const t=audioCtx.currentTime;
    // Low vibrating growl
    const o=audioCtx.createOscillator(), lfo=audioCtx.createOscillator();
    const lfoGain=audioCtx.createGain(), g=audioCtx.createGain();
    lfo.frequency.value=3+intensity*4;
    lfoGain.gain.value=15*intensity;
    lfo.connect(lfoGain); lfoGain.connect(o.frequency);
    o.connect(g); g.connect(audioCtx.destination);
    o.type='sawtooth'; o.frequency.value=38+intensity*20;
    g.gain.setValueAtTime(intensity*0.25,t);
    g.gain.exponentialRampToValueAtTime(0.001,t+0.6);
    lfo.start(t); lfo.stop(t+0.65);
    o.start(t); o.stop(t+0.65);
}

// Whisper sound — the labyrinth speaks
function playWhisper(text, volume=0.08){
    if(!audioCtx) return;
    const t=audioCtx.currentTime;
    // Breathey noise shaped into whisper-frequency band
    for(let i=0;i<3;i++){
        const ns=audioCtx.createBufferSource(), nf=audioCtx.createBiquadFilter(), ng=audioCtx.createGain();
        ns.buffer=noise(1.5+Math.random()*0.5);
        nf.type='bandpass';
        nf.frequency.value=1800+Math.random()*800;
        nf.Q.value=12+Math.random()*8;
        ns.connect(nf); nf.connect(ng); ng.connect(audioCtx.destination);
        const delay=i*0.08;
        ng.gain.setValueAtTime(0,t+delay);
        ng.gain.linearRampToValueAtTime(volume*0.5,t+delay+0.15);
        ng.gain.setValueAtTime(volume,t+delay+0.3);
        ng.gain.exponentialRampToValueAtTime(0.001,t+delay+1.2+Math.random()*0.4);
        ns.start(t+delay); ns.stop(t+delay+2.0);
    }
    // Brief reverb-like noise tail
    const rev=audioCtx.createBufferSource(), rf=audioCtx.createBiquadFilter(), rg=audioCtx.createGain();
    rev.buffer=noise(0.8); rf.type='highpass'; rf.frequency.value=3500;
    rev.connect(rf); rf.connect(rg); rg.connect(audioCtx.destination);
    rg.gain.setValueAtTime(volume*0.3,t+0.6);
    rg.gain.exponentialRampToValueAtTime(0.001,t+1.8);
    rev.start(t+0.6); rev.stop(t+2.0);
}

// False footstep sound
function playFalseStep(){
    if(!audioCtx) return;
    const t=audioCtx.currentTime;
    const o=audioCtx.createOscillator(), g=audioCtx.createGain();
    o.connect(g); g.connect(audioCtx.destination);
    o.type='sine'; o.frequency.setValueAtTime(65,t);
    o.frequency.exponentialRampToValueAtTime(22,t+0.18);
    g.gain.setValueAtTime(0.12,t);
    g.gain.exponentialRampToValueAtTime(0.001,t+0.2);
    o.start(t); o.stop(t+0.21);
}

// Switch activation sound
function playSwitchActivate(){
    if(!audioCtx) return;
    const t=audioCtx.currentTime;
    [220,330,180].forEach((f,i)=>{
        const o=audioCtx.createOscillator(), g=audioCtx.createGain();
        o.connect(g); g.connect(audioCtx.destination);
        o.type='square'; o.frequency.value=f;
        const s=t+i*0.06;
        g.gain.setValueAtTime(0.12,s); g.gain.exponentialRampToValueAtTime(0.001,s+0.25);
        o.start(s); o.stop(s+0.28);
    });
}

// ═══════════════════════════════════════════
// 5. TEXTURES
// ═══════════════════════════════════════════
const wallTex = (()=>{
    const c=document.createElement('canvas'); c.width=TEXSZ; c.height=TEXSZ;
    const x=c.getContext('2d');
    x.fillStyle='#080810'; x.fillRect(0,0,TEXSZ,TEXSZ);
    for(let i=0;i<3000;i++){
        const v=Math.floor(Math.random()*28+3).toString(16).padStart(2,'0');
        x.fillStyle=`#${v}${v}${v}`;
        x.fillRect(Math.random()*TEXSZ,Math.random()*TEXSZ,Math.random()<0.1?2:1,Math.random()<0.1?2:1);
    }
    const BW=32, BH=28;
    x.strokeStyle='rgba(0,0,18,0.9)'; x.lineWidth=2;
    for(let row=0;row<TEXSZ/BH+1;row++){
        const y2=row*BH; const offset=(row%2)*BW*0.5;
        x.beginPath(); x.moveTo(0,y2); x.lineTo(TEXSZ,y2); x.stroke();
        for(let col=-1;col<TEXSZ/BW+1;col++){
            const vx=offset+col*BW;
            x.beginPath(); x.moveTo(vx,y2); x.lineTo(vx,y2+BH); x.stroke();
        }
    }
    x.strokeStyle='rgba(0,0,10,0.6)'; x.lineWidth=1;
    for(let i=0;i<6;i++){
        const sx=Math.random()*TEXSZ, sy=Math.random()*TEXSZ;
        x.beginPath(); x.moveTo(sx,sy);
        x.lineTo(sx+Math.random()*20-10,sy+Math.random()*20-10);
        x.stroke();
    }
    const g=x.createLinearGradient(0,TEXSZ*0.55,0,TEXSZ);
    g.addColorStop(0,'rgba(0,20,0,0)'); g.addColorStop(1,'rgba(0,30,10,0.4)');
    x.fillStyle=g; x.fillRect(0,0,TEXSZ,TEXSZ);
    x.strokeStyle='rgba(0,160,255,0.06)'; x.lineWidth=1;
    for(let i=0;i<3;i++){
        const py=Math.random()*TEXSZ*0.3;
        x.beginPath(); x.moveTo(0,py); x.lineTo(Math.random()*30,py); x.stroke();
    }
    return c;
})();

const doorTex = (()=>{
    const c=document.createElement('canvas'); c.width=TEXSZ; c.height=TEXSZ;
    const x=c.getContext('2d');
    x.fillStyle='#0a0800'; x.fillRect(0,0,TEXSZ,TEXSZ);
    const pGrd=x.createLinearGradient(0,0,TEXSZ,TEXSZ);
    pGrd.addColorStop(0,'#1c1400'); pGrd.addColorStop(0.5,'#2e2000'); pGrd.addColorStop(1,'#1c1400');
    x.fillStyle=pGrd; x.fillRect(6,6,TEXSZ-12,TEXSZ-12);
    x.strokeStyle='#ffd700'; x.lineWidth=2.5;
    x.strokeRect(6,6,TEXSZ-12,TEXSZ-12);
    x.strokeStyle='rgba(255,215,0,0.3)'; x.lineWidth=1;
    x.strokeRect(10,10,TEXSZ-20,TEXSZ-20);
    x.beginPath(); x.arc(TEXSZ/2,20,22,Math.PI,0);
    x.strokeStyle='rgba(255,215,0,0.5)'; x.lineWidth=1.5; x.stroke();
    x.fillStyle='rgba(255,215,0,0.75)';
    x.font='bold 11px serif'; x.textAlign='center';
    const runes=['✦','☽','✦','⬡','✦'];
    runes.forEach((r,i)=>{ x.fillText(r,TEXSZ/2,22+i*21); });
    x.fillStyle='rgba(255,215,0,0.9)';
    x.beginPath(); x.arc(TEXSZ/2,100,6,0,Math.PI*2); x.fill();
    x.fillStyle='rgba(255,215,0,0.7)';
    x.fillRect(TEXSZ/2-3,100,6,12);
    const rg=x.createRadialGradient(TEXSZ/2,TEXSZ/2,2,TEXSZ/2,TEXSZ/2,40);
    rg.addColorStop(0,'rgba(255,215,0,0.18)'); rg.addColorStop(1,'rgba(255,215,0,0)');
    x.fillStyle=rg; x.fillRect(0,0,TEXSZ,TEXSZ);
    return c;
})();

// Switch/lever texture
const switchTex = (()=>{
    const c=document.createElement('canvas'); c.width=TEXSZ; c.height=TEXSZ;
    const x=c.getContext('2d');
    x.fillStyle='#0e0e16'; x.fillRect(0,0,TEXSZ,TEXSZ);
    // Panel
    x.fillStyle='#181820'; x.fillRect(12,10,TEXSZ-24,TEXSZ-20);
    x.strokeStyle='rgba(0,180,255,0.5)'; x.lineWidth=2;
    x.strokeRect(12,10,TEXSZ-24,TEXSZ-20);
    // Lever base
    x.fillStyle='#333'; x.fillRect(TEXSZ/2-10,80,20,16); 
    // Lever handle (pointing UP = inactive)
    x.strokeStyle='#00ccff'; x.lineWidth=6; x.lineCap='round';
    x.beginPath(); x.moveTo(TEXSZ/2,90); x.lineTo(TEXSZ/2,40); x.stroke();
    // Glow indicator
    const rg=x.createRadialGradient(TEXSZ/2,36,2,TEXSZ/2,36,18);
    rg.addColorStop(0,'rgba(0,200,255,0.9)'); rg.addColorStop(1,'rgba(0,200,255,0)');
    x.fillStyle=rg; x.fillRect(TEXSZ/2-18,18,36,36);
    // Circle cap
    x.fillStyle='#00ccff';
    x.beginPath(); x.arc(TEXSZ/2,36,7,0,Math.PI*2); x.fill();
    // Warning text
    x.fillStyle='rgba(0,180,255,0.4)';
    x.font='bold 9px monospace'; x.textAlign='center';
    x.fillText('ACTIVA',TEXSZ/2,TEXSZ-14);
    return c;
})();

const keySpriteTex = (()=>{
    const c=document.createElement('canvas'); c.width=64; c.height=32;
    const x=c.getContext('2d');
    x.clearRect(0,0,64,32);
    x.fillStyle='rgba(0,0,0,0.5)';
    x.beginPath(); x.ellipse(32,26,22,5,0,0,Math.PI*2); x.fill();
    const grad=x.createLinearGradient(10,16,54,16);
    grad.addColorStop(0,'#c8a000'); grad.addColorStop(0.4,'#ffe566'); grad.addColorStop(1,'#a07800');
    x.strokeStyle=grad; x.lineWidth=5; x.lineCap='round';
    x.beginPath(); x.moveTo(12,16); x.lineTo(50,16); x.stroke();
    x.strokeStyle='#ffe566'; x.lineWidth=4;
    x.beginPath(); x.arc(12,16,8,0,Math.PI*2); x.stroke();
    x.fillStyle='#20150a';
    x.beginPath(); x.arc(12,16,4,0,Math.PI*2); x.fill();
    x.strokeStyle='#c8a000'; x.lineWidth=3; x.lineCap='square';
    [[44,16,44,22],[38,16,38,20],[50,16,50,19]].forEach(([x1,y1,x2,y2])=>{
        x.beginPath(); x.moveTo(x1,y1); x.lineTo(x2,y2); x.stroke();
    });
    x.strokeStyle='rgba(255,255,200,0.5)'; x.lineWidth=1.5;
    x.beginPath(); x.moveTo(16,13); x.lineTo(46,13); x.stroke();
    return c;
})();

const enemyTex = (()=>{
    const c=document.createElement('canvas'); c.width=96; c.height=192;
    const x=c.getContext('2d');
    x.fillStyle='#0d0000';
    x.beginPath(); x.ellipse(48,28,18,24,0,0,Math.PI*2); x.fill();
    const hood=x.createRadialGradient(48,28,4,48,28,24);
    hood.addColorStop(0,'rgba(40,0,0,0.5)'); hood.addColorStop(1,'rgba(0,0,0,0)');
    x.fillStyle=hood; x.beginPath(); x.ellipse(48,28,18,24,0,0,Math.PI*2); x.fill();
    x.fillStyle='rgba(200,0,0,0.0)';
    const torsoGrd=x.createLinearGradient(30,50,66,160);
    torsoGrd.addColorStop(0,'#160000'); torsoGrd.addColorStop(1,'#080000');
    x.fillStyle=torsoGrd;
    x.beginPath();
    x.moveTo(30,52); x.lineTo(66,52); x.lineTo(72,155); x.lineTo(24,155); x.closePath();
    x.fill();
    x.strokeStyle='rgba(30,0,0,0.8)'; x.lineWidth=1.5;
    [[38,55,34,155],[48,52,48,155],[58,55,62,155]].forEach(([x1,y1,x2,y2])=>{
        x.beginPath(); x.moveTo(x1,y1); x.lineTo(x2,y2); x.stroke();
    });
    x.strokeStyle='#110000'; x.lineWidth=10; x.lineCap='round';
    x.beginPath(); x.moveTo(32,60); x.quadraticCurveTo(14,100,10,130); x.stroke();
    x.beginPath(); x.moveTo(64,60); x.quadraticCurveTo(82,100,86,130); x.stroke();
    x.strokeStyle='#2a0000'; x.lineWidth=2;
    [[10,130,6,140],[10,130,10,142],[10,130,14,140]].forEach(([x1,y1,x2,y2])=>{
        x.beginPath(); x.moveTo(x1,y1); x.lineTo(x2,y2); x.stroke();
    });
    [[86,130,82,140],[86,130,86,142],[86,130,90,140]].forEach(([x1,y1,x2,y2])=>{
        x.beginPath(); x.moveTo(x1,y1); x.lineTo(x2,y2); x.stroke();
    });
    x.fillStyle='#0a0000';
    x.beginPath();
    x.moveTo(24,155); x.lineTo(72,155); x.lineTo(66,192); x.lineTo(30,192); x.closePath();
    x.fill();
    return c;
})();

// ═══════════════════════════════════════════
// 6. DUNGEON GENERATOR
// ═══════════════════════════════════════════
function randInt(a,b){ return Math.floor(Math.random()*(b-a))+a; }

function generateDungeon(){
    map = Array.from({length:MAPSZ},()=>Array(MAPSZ).fill(WALL));
    keyItems=[]; doorPos=null; doorWallSide=null; switchItems=[];

    const rooms=[];
    for(let attempt=0;attempt<35;attempt++){
        const w=randInt(6,12), h=randInt(6,12);
        const rx=randInt(2,MAPSZ-w-3), ry=randInt(2,MAPSZ-h-3);
        let ok=true;
        for(const r of rooms){
            if(rx<r.x+r.w+2&&rx+w+2>r.x&&ry<r.y+r.h+2&&ry+h+2>r.y){ok=false;break;}
        }
        if(ok){
            for(let y=ry;y<ry+h;y++) for(let x=rx;x<rx+w;x++) map[y][x]=FLOOR;
            rooms.push({x:rx,y:ry,w,h,cx:rx+Math.floor(w/2),cy:ry+Math.floor(h/2)});
        }
    }
    if(rooms.length<3){
        [[2,2,9,9],[22,5,9,9],[42,2,9,9],[2,28,9,9],[42,28,9,9],[22,40,9,9]].forEach(([rx,ry,w,h])=>{
            for(let y=ry;y<ry+h;y++) for(let x=rx;x<rx+w;x++) map[y][x]=FLOOR;
            rooms.push({x:rx,y:ry,w,h,cx:rx+Math.floor(w/2),cy:ry+Math.floor(h/2)});
        });
    }
    for(let i=0;i<rooms.length-1;i++) connectRooms(rooms[i],rooms[i+1]);
    // Extra anti-labyrinth carve passes for natural shapes
    for(let n=0;n<Math.floor(MAPSZ*1.8);n++){
        const cx=randInt(2,MAPSZ-2), cy=randInt(2,MAPSZ-2);
        if(Math.random()<0.65){
            for(let y=-1;y<=1;y++) for(let x=-1;x<=1;x++) if(map[cy+y]&&map[cy+y][cx+x]===WALL&&Math.random()<0.55) map[cy+y][cx+x]=FLOOR;
        }
    }
    for(let i=0;i<Math.floor(rooms.length*0.4);i++){
        const a=rooms[randInt(0,rooms.length)], b=rooms[randInt(0,rooms.length)];
        if(a!==b) connectRooms(a,b);
    }

    const sr=rooms[0];
    player.x=(sr.cx+0.5)*TILE; player.y=(sr.cy+0.5)*TILE;
    cameraAngle=Math.random()*Math.PI*2;
    player.speed=0;

    const er=rooms[rooms.length-1];
    const dgy=er.y+er.h;
    const dgx=er.cx;
    if(dgy<MAPSZ){ map[dgy][dgx]=DOOR; doorPos={gx:dgx,gy:dgy}; doorWallSide='S'; }
    else { map[er.cy][er.cx]=DOOR; doorPos={gx:er.cx,gy:er.cy}; doorWallSide='N'; }

    // ── Assign mission objective ──
    assignObjective(rooms);

    // Enemy
    const enri=Math.max(1,Math.floor(rooms.length*0.5));
    const enr=rooms[enri];
    enemy.x=(enr.cx+0.5)*TILE; enemy.y=(enr.cy+0.5)*TILE;
    enemy.speed=1.1+level*0.15;
    enemy.active=true; enemy.state='patrol';
    enemy.faceAngle=Math.random()*Math.PI*2;
    enemy.alertTimer=0; enemy.searchTimer=0;
    enemy.chaseTimer=0; enemy.chargeTimer=0;
    enemy.ambushArmed=false; enemy.ambushNode=null;

    // Build patrol nodes for advanced AI
    buildPatrolNodes(rooms);

    // Place ghosts
    ghosts=[];
    spawnGhost(rooms);

    mapRooms = rooms;
    lampSources = buildLampSources(rooms);

    if(level===1){ inventory.keys=0; updateInventoryUI(); }
}

function assignObjective(rooms){
    // Level-based objectives
    const missionPool = [
        { type:'keys', required: Math.max(1, Math.floor(rooms.length/3)), label: null },
        { type:'switches', required: 2, label: 'Activa 2 interruptores' },
        { type:'survive', required: 40+level*5, label: null },
        { type:'keys', required: Math.min(3, Math.max(1, Math.floor(rooms.length/4))), label: null },
    ];

    // Level 1 always keys
    let mission;
    if(level===1){
        mission = { type:'keys', required:1 };
    } else {
        mission = missionPool[Math.floor(Math.random()*missionPool.length)];
    }

    mission.done = false;
    mission.progress = 0;

    if(mission.type==='keys'){
        mission.label = mission.required===1 ? 'Encuentra la llave' : `Encuentra ${mission.required} llaves`;
        // Place keys
        const keyCount=mission.required;
        const used=new Set([0,rooms.length-1]);
        let placed=0;
        for(let ri=1;ri<rooms.length-1&&placed<keyCount;ri++){
            if(used.has(ri)) continue;
            used.add(ri);
            const kr=rooms[ri];
            const kgx=kr.cx+randInt(-1,2), kgy=kr.cy+randInt(-1,2);
            if(map[kgy]&&map[kgy][kgx]===FLOOR){
                map[kgy][kgx]=KEY;
                keyItems.push({gx:kgx,gy:kgy,wx:(kgx+0.5)*TILE,wy:(kgy+0.5)*TILE,collected:false});
                placed++;
            }
        }
        if(placed===0){
            const kr=rooms[1];
            map[kr.cy][kr.cx]=KEY;
            keyItems.push({gx:kr.cx,gy:kr.cy,wx:(kr.cx+0.5)*TILE,wy:(kr.cy+0.5)*TILE,collected:false});
        }
        mission.required=Math.max(1,placed);
    } else if(mission.type==='switches'){
        // Place switches in random rooms
        const reqCount=Math.min(2,rooms.length-2);
        mission.required=reqCount;
        const used=new Set([0,rooms.length-1]);
        let placed=0;
        for(let ri=1;ri<rooms.length-1&&placed<reqCount;ri++){
            if(Math.random()<0.4&&!used.has(ri)){
                used.add(ri);
                const kr=rooms[ri];
                // Place on a wall tile next to the room
                const sgx=kr.cx, sgy=kr.y-1;
                if(sgy>=0&&map[sgy]&&map[sgy][sgx]===WALL){
                    map[sgy][sgx]=SWITCH_TILE;
                    switchItems.push({gx:sgx,gy:sgy,wx:(sgx+0.5)*TILE,wy:(sgy+0.5)*TILE,activated:false});
                    placed++;
                }
            }
        }
        if(placed===0){
            const kr=rooms[1];
            const sgx=kr.cx, sgy=kr.y-1;
            if(sgy>=0) { map[sgy][sgx]=SWITCH_TILE; switchItems.push({gx:sgx,gy:sgy,wx:(sgx+0.5)*TILE,wy:(sgy+0.5)*TILE,activated:false}); placed=1; }
        }
        mission.required=Math.max(1,placed);
        mission.label=`Activa ${mission.required} interruptor${mission.required>1?'es':''}`;
    } else if(mission.type==='survive'){
        mission.label=`Sobrevive ${mission.required}s al acecho`;
        surviveChaseSecs=0;
        // Also place one key as a bonus
        const kr=rooms[Math.max(1,Math.floor(rooms.length/2))];
        const kgx=kr.cx, kgy=kr.cy;
        if(map[kgy]&&map[kgy][kgx]===FLOOR){
            map[kgy][kgx]=KEY;
            keyItems.push({gx:kgx,gy:kgy,wx:(kgx+0.5)*TILE,wy:(kgy+0.5)*TILE,collected:false});
        }
    }

    currentObjective = mission;
    objectiveDone = false;
    updateObjectiveHUD();
}

function connectRooms(r1,r2){
    let cx=r1.cx, cy=r1.cy;
    const xd=r2.cx>cx?1:-1;
    while(cx!==r2.cx){ safeFloor(cy,cx); cx+=xd; }
    const yd=r2.cy>cy?1:-1;
    while(cy!==r2.cy){ safeFloor(cy,cx); cy+=yd; }
    safeFloor(cy,cx);
}
function safeFloor(y,x){
    if(y>=0&&y<MAPSZ&&x>=0&&x<MAPSZ&&map[y][x]===WALL) map[y][x]=FLOOR;
}

function buildLampSources(rooms){
    const lamps=[];
    for(const r of rooms.slice(1,-1)){
        if(Math.random()<0.7){
            lamps.push({x:(r.cx+0.5)*TILE,y:(r.cy+0.5)*TILE,flicker:Math.random()<0.55,phase:Math.random()*Math.PI*2,intensity:0.7+Math.random()*0.5});
        }
    }
    return lamps;
}

// ═══════════════════════════════════════════
// 6b. NODE GRAPH FOR AI PATROL
// ═══════════════════════════════════════════
function buildPatrolNodes(rooms){
    // Sample room centers as patrol nodes
    enemy.patrolNodes = rooms.slice(1,-1).map(r=>({x:(r.cx+0.5)*TILE, y:(r.cy+0.5)*TILE}));
    // Shuffle
    for(let i=enemy.patrolNodes.length-1;i>0;i--){
        const j=randInt(0,i+1);
        [enemy.patrolNodes[i],enemy.patrolNodes[j]]=[enemy.patrolNodes[j],enemy.patrolNodes[i]];
    }
    enemy.patrolIdx=0;
    // Pick an ambush node (near door or a corner room)
    if(enemy.patrolNodes.length>0){
        enemy.ambushNode = enemy.patrolNodes[randInt(0,Math.min(3,enemy.patrolNodes.length))];
    }
}

// Ghost apparition
function spawnGhost(rooms){
    if(rooms.length<3) return;
    const ri=randInt(1,rooms.length-1);
    const r=rooms[ri];
    ghosts.push({
        x:(r.cx+0.5+Math.random()-0.5)*TILE,
        y:(r.cy+0.5+Math.random()-0.5)*TILE,
        timer:8+Math.random()*8,
        opacity:0,
        state:'fade_in',   // fade_in | visible | fade_out
        angle:Math.random()*Math.PI*2,
    });
}

// ═══════════════════════════════════════════
// 7. COLLISION
// ═══════════════════════════════════════════
const PRAD=16;

function cellSolid(wx,wy){
    const gx=Math.floor(wx/TILE), gy=Math.floor(wy/TILE);
    if(gx<0||gx>=MAPSZ||gy<0||gy>=MAPSZ) return true;
    const c=map[gy][gx];
    return c===WALL;
}
function tryMove(ox,oy,dx,dy){
    const r=PRAD;
    const nx=ox+dx, ny=oy+dy;
    const okX = !cellSolid(nx+r,oy+r)&&!cellSolid(nx+r,oy-r)&&
                !cellSolid(nx-r,oy+r)&&!cellSolid(nx-r,oy-r);
    const okY = !cellSolid(ox+r,ny+r)&&!cellSolid(ox+r,ny-r)&&
                !cellSolid(ox-r,ny+r)&&!cellSolid(ox-r,ny-r);
    return { x: okX?nx:ox, y: okY?ny:oy };
}
function enemySolid(wx,wy){
    const gx=Math.floor(wx/TILE), gy=Math.floor(wy/TILE);
    if(gx<0||gx>=MAPSZ||gy<0||gy>=MAPSZ) return true;
    return map[gy][gx]===WALL;
}

// ═══════════════════════════════════════════
// 8. LINE OF SIGHT
// ═══════════════════════════════════════════
function hasLOS(ax,ay,bx,by){
    const steps=80;
    for(let i=1;i<steps;i++){
        const t=i/steps;
        const gx=Math.floor((ax+(bx-ax)*t)/TILE);
        const gy=Math.floor((ay+(by-ay)*t)/TILE);
        if(gx<0||gx>=MAPSZ||gy<0||gy>=MAPSZ) return false;
        if(map[gy][gx]===WALL) return false;
    }
    return true;
}

// ═══════════════════════════════════════════
// 9. ENEMY AI — ADVANCED
// ═══════════════════════════════════════════
function updateEnemy(dt){
    if(!enemy.active) return;
    const dx=player.x-enemy.x, dy=player.y-enemy.y;
    const dist=Math.hypot(dx,dy);
    const toPlayer=Math.atan2(dy,dx);
    let diff=toPlayer-enemy.faceAngle;
    while(diff>Math.PI) diff-=Math.PI*2;
    while(diff<-Math.PI) diff+=Math.PI*2;

    const isHoldingBreath = breathState.holding;
    const speedNoise = Math.abs(player.speed)>0.5;
    const runningLoud = Math.abs(player.speed)>(SPEED_WALK+0.2);
    const inCone = Math.abs(diff)<enemy.visionAngle*0.5 && dist<enemy.visionRadius;
    const los    = dist<enemy.visionRadius && hasLOS(enemy.x,enemy.y,player.x,player.y);
    // Sin linterna y sin correr, el enemigo no debería detectar de forma injusta.
    const canVisuallyDetect = lantern.on || dist<140 || enemy.state==='chase';
    const inHear = !isHoldingBreath && dist<enemy.hearingRadius && (runningLoud || (speedNoise&&lantern.on));
    const detected = (inCone&&los&&canVisuallyDetect)||(inHear&&los);

    enemy.walkPhase += enemy.speed * dt * 0.12;

    // Predict player position
    const playerVx=Math.cos(cameraAngle)*player.speed;
    const playerVy=Math.sin(cameraAngle)*player.speed;
    const predT=Math.min(0.8, dist/600);
    enemy.predictX=player.x+playerVx*predT*60;
    enemy.predictY=player.y+playerVy*predT*60;

    // Growl when chasing close
    if(enemy.state==='chase'){
        enemy.chaseTimer+=dt;
        if(enemy.chaseTimer>1.2&&dist<350){
            playEnemyGrowl(Math.max(0.3,1-dist/350));
            enemy.chaseTimer=0;
        }
        // Update survive objective
        if(currentObjective&&currentObjective.type==='survive'){
            surviveChaseSecs+=dt;
        }
    }

    switch(enemy.state){
        case 'idle':
            enemy.alertTimer-=dt;
            if(detected){ enemy.state='chase'; }
            else if(enemy.alertTimer<=0){ enemy.state='patrol'; enemy.alertTimer=randInt(2,6); }
            break;

        case 'patrol':
            // Node-based patrol
            if(enemy.patrolNodes.length>0){
                const node=enemy.patrolNodes[enemy.patrolIdx % enemy.patrolNodes.length];
                const ndx=node.x-enemy.x, ndy=node.y-enemy.y;
                const ndist=Math.hypot(ndx,ndy);
                if(ndist<TILE*0.8){
                    enemy.patrolIdx++;
                    // Occasionally arm ambush
                    if(Math.random()<0.3&&enemy.ambushNode&&!enemy.ambushArmed){
                        enemy.state='ambush';
                        break;
                    }
                } else {
                    const a=Math.atan2(ndy,ndx);
                    enemy.faceAngle=a;
                    let ld=diff; while(ld>Math.PI)ld-=Math.PI*2; while(ld<-Math.PI)ld+=Math.PI*2;
                    enemy.faceAngle+=Math.sin(enemy.walkPhase*0.3)*0.08;
                    const pm=enemy.speed*0.55;
                    const pmx=Math.cos(a)*pm, pmy=Math.sin(a)*pm;
                    if(!enemySolid(enemy.x+pmx,enemy.y)) enemy.x+=pmx;
                    else enemy.faceAngle+=Math.PI*0.5+Math.random()*0.5;
                    if(!enemySolid(enemy.x,enemy.y+pmy)) enemy.y+=pmy;
                    else enemy.faceAngle+=Math.PI*0.5+Math.random()*0.5;
                }
            } else {
                enemy.faceAngle += 0.35*dt + Math.sin(enemy.walkPhase)*0.1;
                const pm=enemy.speed*0.45;
                const pmx=Math.cos(enemy.faceAngle)*pm, pmy=Math.sin(enemy.faceAngle)*pm;
                if(!enemySolid(enemy.x+pmx,enemy.y)) enemy.x+=pmx;
                else enemy.faceAngle+=Math.PI*0.5+Math.random()*0.5;
                if(!enemySolid(enemy.x,enemy.y+pmy)) enemy.y+=pmy;
                else enemy.faceAngle+=Math.PI*0.5+Math.random()*0.5;
            }
            if(detected){ enemy.state='chase'; enemy.chaseTimer=0; }
            break;

        case 'ambush':
            // Move silently to ambush position, then wait
            if(enemy.ambushNode){
                const adx=enemy.ambushNode.x-enemy.x, ady=enemy.ambushNode.y-enemy.y;
                const adist=Math.hypot(adx,ady);
                if(adist>TILE*0.6){
                    const a=Math.atan2(ady,adx); enemy.faceAngle=a;
                    const pm=enemy.speed*0.3; // creep silently
                    if(!enemySolid(enemy.x+Math.cos(a)*pm,enemy.y)) enemy.x+=Math.cos(a)*pm;
                    if(!enemySolid(enemy.x,enemy.y+Math.sin(a)*pm)) enemy.y+=Math.sin(a)*pm;
                } else {
                    enemy.ambushArmed=true;
                    enemy.alertTimer=4+Math.random()*4; // wait in hiding
                    enemy.state='ambush_wait';
                }
            } else enemy.state='patrol';
            if(detected){ enemy.state='chase'; enemy.chaseTimer=0; }
            break;

        case 'ambush_wait':
            enemy.alertTimer-=dt;
            // Face toward player silently
            const awang=Math.atan2(dy,dx);
            enemy.faceAngle=awang; // stare but don't move
            if(dist<enemy.visionRadius*0.8&&los){
                // CHARGE! Lunge at player
                enemy.state='chase';
                enemy.chargeTimer=0.7; // brief charge boost
                enemy.chaseTimer=0;
                // Play surprise jump scare sound
                playEnemyGrowl(1.0);
            }
            if(enemy.alertTimer<=0){ enemy.state='patrol'; enemy.ambushArmed=false; }
            break;

        case 'chase':
            // Use predicted position
            const tgtX = dist<200 ? player.x : enemy.predictX;
            const tgtY = dist<200 ? player.y : enemy.predictY;
            if(!detected&&dist>enemy.visionRadius*1.15){
                enemy.state='search';
                enemy.lastSeenX=player.x; enemy.lastSeenY=player.y;
                enemy.searchTimer=6+Math.random()*4;
                enemy.chaseTimer=0;
            } else {
                enemy.chargeTimer=Math.max(0,enemy.chargeTimer-dt);
                const chargeBoost=enemy.chargeTimer>0?1.6:1.0;
                const spd=enemy.speed*(dist<200?1.3:1.0)*chargeBoost;
                const ang=Math.atan2(tgtY-enemy.y, tgtX-enemy.x);
                enemy.faceAngle=ang;
                const mx=Math.cos(ang)*spd, my=Math.sin(ang)*spd;
                if(!enemySolid(enemy.x+mx,enemy.y)) enemy.x+=mx;
                else if(!enemySolid(enemy.x+mx*0.3,enemy.y+my*0.3)){ enemy.x+=mx*0.3; enemy.y+=my*0.3; }
                else enemy.faceAngle+=0.15;
                if(!enemySolid(enemy.x,enemy.y+my)) enemy.y+=my;
                else enemy.faceAngle-=0.15;
            }
            break;

        case 'search':
            enemy.searchTimer-=dt;
            const sdx=enemy.lastSeenX-enemy.x, sdy=enemy.lastSeenY-enemy.y;
            const sd=Math.hypot(sdx,sdy);
            if(sd>50){
                const a=Math.atan2(sdy,sdx); enemy.faceAngle=a;
                const mx=Math.cos(a)*enemy.speed*0.65, my=Math.sin(a)*enemy.speed*0.65;
                if(!enemySolid(enemy.x+mx,enemy.y)) enemy.x+=mx;
                if(!enemySolid(enemy.x,enemy.y+my)) enemy.y+=my;
            }
            if(detected){ enemy.state='chase'; enemy.chaseTimer=0; }
            else if(enemy.searchTimer<=0){ enemy.state='idle'; enemy.alertTimer=2+Math.random()*3; }
            break;
    }
}

// ═══════════════════════════════════════════
// 9b. GHOST APPARITIONS
// ═══════════════════════════════════════════
function updateGhosts(dt){
    for(let i=ghosts.length-1;i>=0;i--){
        const g=ghosts[i];
        g.timer-=dt;
        if(g.state==='fade_in'){
            g.opacity=Math.min(0.85, g.opacity+dt*0.8);
            if(g.opacity>=0.85) g.state='visible';
        } else if(g.state==='visible'){
            if(g.timer<2) g.state='fade_out';
            // Move slightly
            const ang=g.angle+Math.sin(gameTime*0.5)*0.3;
            const spd=0.3;
            if(!cellSolid(g.x+Math.cos(ang)*spd,g.y)) g.x+=Math.cos(ang)*spd;
            if(!cellSolid(g.x,g.y+Math.sin(ang)*spd)) g.y+=Math.sin(ang)*spd;

            // If player shines lantern at ghost, it vanishes
            if(lantern.on){
                const gdx=g.x-player.x, gdy=g.y-player.y;
                let gsa=Math.atan2(gdy,gdx)-cameraAngle;
                while(gsa<-Math.PI) gsa+=Math.PI*2;
                while(gsa>Math.PI) gsa-=Math.PI*2;
                if(Math.abs(gsa)<FOV*0.4&&Math.hypot(gdx,gdy)<350){
                    g.state='fade_out';
                    g.timer=Math.min(g.timer,1.5);
                }
            }
        } else if(g.state==='fade_out'){
            g.opacity=Math.max(0, g.opacity-dt*1.2);
            if(g.opacity<=0){ ghosts.splice(i,1); continue; }
        }
        if(g.timer<=0 && g.state!=='fade_out'){ g.state='fade_out'; g.timer=1.5; }
    }
}

// ═══════════════════════════════════════════
// 9c. SANITY SYSTEM
// ═══════════════════════════════════════════
function updateSanity(dt, dist){
    const inDarkness = !lantern.on && lantern.battery<50;
    const nearEnemy  = dist < 400;
    const chasing    = enemy.state==='chase';

    if((inDarkness||nearEnemy)&&chasing){
        sanity.value=Math.max(0, sanity.value + sanity.rate*dt*(chasing?1.8:1.0));
    } else if(!nearEnemy&&lantern.on){
        sanity.value=Math.min(100, sanity.value + sanity.regenRate*dt);
    } else if(!nearEnemy){
        sanity.value=Math.min(100, sanity.value + sanity.regenRate*0.3*dt);
    }

    sanity.distortion = Math.pow(Math.max(0,(50-sanity.value)/50), 1.5);
}

// ═══════════════════════════════════════════
// 9d. FEAR DIRECTOR
// ═══════════════════════════════════════════
function updateFearDirector(dt, dist){
    // Calculate tension
    const distFactor   = Math.max(0, 1-dist/700);
    const sanityFactor = Math.max(0,(50-sanity.value)/50);
    const battFactor   = Math.max(0,(30-lantern.battery)/30);
    fearDirector.tension = Math.min(100,
        distFactor*40 + sanityFactor*30 + battFactor*20 +
        (enemy.state==='chase'?30:0)
    );

    fearDirector.eventCooldown=Math.max(0,fearDirector.eventCooldown-dt);

    // Silence mode
    if(fearDirector.silenceActive){
        fearDirector.silenceTimer-=dt;
        if(fearDirector.silenceTimer<=0){
            fearDirector.silenceActive=false;
            // After silence: burst scare
            if(fearDirector.tension>50&&dist>300){
                triggerHorrorEvent('false_footstep');
            }
        }
    }

    // Trigger events based on tension
    if(fearDirector.eventCooldown<=0&&fearDirector.tension>30){
        const roll=Math.random();
        const tensionNorm=fearDirector.tension/100;
        if(roll<0.008*tensionNorm){
            const events=['light_flicker','false_footstep','distortion_flash','whisper_event'];
            const pick=events[Math.floor(Math.random()*events.length)];
            triggerHorrorEvent(pick);
            fearDirector.eventCooldown=8+Math.random()*12;
        }
        // Silence periods at medium tension
        if(roll<0.003&&fearDirector.tension>40&&!fearDirector.silenceActive){
            fearDirector.silenceActive=true;
            fearDirector.silenceTimer=3+Math.random()*4;
        }
    }
}

function triggerHorrorEvent(type){
    if(type==='light_flicker'){
        horrorEvents.push({type:'flicker', timer:0.8+Math.random()*0.6, data:{phase:0}});
    } else if(type==='false_footstep'){
        horrorEvents.push({type:'false_step', timer:0.1, data:{}});
        playFalseStep();
        // Sometimes play a second step
        if(Math.random()<0.5) setTimeout(()=>playFalseStep(), 350+Math.random()*200);
    } else if(type==='distortion_flash'){
        horrorEvents.push({type:'distort', timer:0.3+Math.random()*0.5, data:{intensity:0.5+Math.random()*0.5}});
    } else if(type==='whisper_event'){
        horrorEvents.push({type:'whisper', timer:2.5, data:{shown:false}});
        playWhisper('...');
        // Show brief text overlay
        const wTexts=[
            '...no puedes escapar...',
            '...te encontraré...',
            '...aquí estás...',
            '...siempre estoy cerca...',
            '...el laberinto es eterno...',
        ];
        const txt=wTexts[Math.floor(Math.random()*wTexts.length)];
        showWhisperText(txt);
    }
}

function updateHorrorEvents(dt){
    for(let i=horrorEvents.length-1;i>=0;i--){
        const ev=horrorEvents[i];
        ev.timer-=dt;
        if(ev.timer<=0){ horrorEvents.splice(i,1); }
    }
    // Schedule whispers at level 1
    if(level===1&&isRunning&&!isPaused){
        whisperTimer-=dt;
        if(whisperTimer<=0){
            playWhisper('',0.06);
            const wTexts=['...no estás solo...','...el laberinto te espera...','...hay algo detrás de ti...'];
            showWhisperText(wTexts[Math.floor(Math.random()*wTexts.length)]);
            whisperTimer=18+Math.random()*22;
        }
    }
}

let whisperTextEl=null;
function showWhisperText(text){
    if(!whisperTextEl){
        whisperTextEl=document.createElement('div');
        whisperTextEl.style.cssText=`
            position:fixed;top:38%;left:50%;transform:translateX(-50%);
            color:rgba(180,0,0,0.7);font-family:'Creepster',cursive;font-size:1.4rem;
            letter-spacing:4px;pointer-events:none;z-index:30;text-align:center;
            text-shadow:0 0 20px rgba(200,0,0,0.6);transition:opacity 0.5s;
            opacity:0;max-width:80vw;
        `;
        document.getElementById('game-container').appendChild(whisperTextEl);
    }
    whisperTextEl.textContent=text;
    whisperTextEl.style.opacity='1';
    clearTimeout(whisperTextEl._timeout);
    whisperTextEl._timeout=setTimeout(()=>{ whisperTextEl.style.opacity='0'; }, 3500);
}

// ═══════════════════════════════════════════
// 10. INPUT — KEYBOARD (WASD = STRAFE/MOVE ONLY)
// ═══════════════════════════════════════════
const keys_held = {};
window.addEventListener('keydown',e=>{ keys_held[e.code]=true; onKeyAction(e); });
window.addEventListener('keyup',  e=>{ keys_held[e.code]=false; });

function onKeyAction(e){
    if(e.code==='Escape'){ togglePause(); return; }
    if(!isRunning||isPaused||isDying) return;
    if(e.code===settings.keys.lantern) toggleLantern();
    if(e.code===settings.keys.pickup)  tryPickup();
}

// CAMERA: mouse only
window.addEventListener('mousemove',e=>{
    if(isRunning&&!isPaused&&!isDying&&document.pointerLockElement===canvas){
        cameraAngle+=e.movementX*settings.mouseSens;
        cameraPitch=Math.max(-MAX_PITCH, Math.min(MAX_PITCH, cameraPitch + e.movementY*settings.mouseSens*0.65));
    }
});
canvas.addEventListener('click',()=>{
    if(isRunning&&!isPaused) canvas.requestPointerLock();
});

// ═══════════════════════════════════════════
// 11. INPUT — MOBILE JOYSTICKS
// ═══════════════════════════════════════════
const joy = {
    left:  { active:false, id:-1, startX:0, startY:0, dx:0, dy:0 },
    right: { active:false, id:-1, startX:0, startY:0, dx:0, dy:0 },
};

const leftZone  = document.getElementById('joystick-left');
const rightZone = document.getElementById('joystick-right');
const knobLeft  = document.getElementById('knob-left');

function joyRadius(){ return 40; }

leftZone.addEventListener('touchstart',e=>{
    e.preventDefault();
    const t=e.changedTouches[0];
    joy.left.active=true; joy.left.id=t.identifier;
    joy.left.startX=t.clientX; joy.left.startY=t.clientY;
    joy.left.dx=0; joy.left.dy=0;
},{passive:false});

leftZone.addEventListener('touchmove',e=>{
    e.preventDefault();
    for(const t of e.changedTouches){
        if(t.identifier===joy.left.id){
            const dx=t.clientX-joy.left.startX, dy=t.clientY-joy.left.startY;
            const len=Math.hypot(dx,dy);
            const r=joyRadius();
            const clamp=Math.min(len,r);
            joy.left.dx=dx/Math.max(len,1)*clamp/r;
            joy.left.dy=dy/Math.max(len,1)*clamp/r;
            knobLeft.style.transform=`translate(${joy.left.dx*r}px,${joy.left.dy*r}px)`;
        }
    }
},{passive:false});

leftZone.addEventListener('touchend',e=>{
    e.preventDefault();
    for(const t of e.changedTouches){
        if(t.identifier===joy.left.id){
            joy.left.active=false; joy.left.dx=0; joy.left.dy=0;
            knobLeft.style.transform='translate(0,0)';
        }
    }
},{passive:false});

rightZone.addEventListener('touchstart',e=>{
    e.preventDefault();
    const t=e.changedTouches[0];
    joy.right.active=true; joy.right.id=t.identifier;
    joy.right.startX=t.clientX; joy.right.startY=t.clientY;
    joy.right.dx=0; joy.right.dy=0;
},{passive:false});

rightZone.addEventListener('touchmove',e=>{
    e.preventDefault();
    for(const t of e.changedTouches){
        if(t.identifier===joy.right.id){
            joy.right.dx=t.clientX-joy.right.startX;
            joy.right.dy=t.clientY-joy.right.startY;
            joy.right.startX=t.clientX; joy.right.startY=t.clientY;
        }
    }
},{passive:false});

rightZone.addEventListener('touchend',e=>{
    e.preventDefault();
    for(const t of e.changedTouches){
        if(t.identifier===joy.right.id){
            joy.right.active=false; joy.right.dx=0; joy.right.dy=0;
        }
    }
},{passive:false});

let mobRunHeld=false;
const mobRun=document.getElementById('mob-run');
const mobLantern=document.getElementById('mob-lantern');
const mobPickup=document.getElementById('mob-pickup');

mobRun.addEventListener('touchstart',e=>{ e.preventDefault(); mobRunHeld=true; mobRun.classList.add('pressed'); ensureAudio(); },{passive:false});
mobRun.addEventListener('touchend',  e=>{ e.preventDefault(); mobRunHeld=false; mobRun.classList.remove('pressed'); },{passive:false});
mobLantern.addEventListener('touchstart',e=>{ e.preventDefault(); ensureAudio(); toggleLantern(); },{passive:false});
mobPickup.addEventListener('touchstart', e=>{ e.preventDefault(); ensureAudio(); tryPickup(); },{passive:false});
document.getElementById('mob-pause').addEventListener('touchstart',e=>{ e.preventDefault(); ensureAudio(); togglePause(); },{passive:false});

// ═══════════════════════════════════════════
// 12. GAME LOGIC UPDATE
// ═══════════════════════════════════════════
function updateLogic(dt){
    // ── Movement — WASD/arrows strafe ONLY (no rotation) ──
    const holdingBreathKey = keys_held['ShiftLeft']||keys_held['ShiftRight']||keys_held['AltLeft']||keys_held['AltRight'];
    breathState.holding = !!holdingBreathKey;

    const sprinting = (keys_held[settings.keys.sprint]||mobRunHeld) && !breathState.holding;
    player.maxSpeed = sprinting ? SPEED_RUN : SPEED_WALK;

    let moveForward = keys_held['KeyW']||keys_held['ArrowUp']   ? 1 : 0;
    let moveBack    = keys_held['KeyS']||keys_held['ArrowDown']  ? 1 : 0;
    let strafeRight = keys_held['KeyD']||keys_held['ArrowRight'] ? 1 : 0;
    let strafeLeft  = keys_held['KeyA']||keys_held['ArrowLeft']  ? 1 : 0;

    // Joystick: left = movement, right = camera
    if(joy.left.active){
        if(joy.left.dy<-0.2) moveForward=Math.abs(joy.left.dy);
        if(joy.left.dy> 0.2) moveBack   =Math.abs(joy.left.dy);
        if(joy.left.dx> 0.2) strafeRight=Math.abs(joy.left.dx)*settings.joyXSens;
        if(joy.left.dx<-0.2) strafeLeft =Math.abs(joy.left.dx)*settings.joyXSens;
    }
    if(joy.right.active){
        cameraAngle += joy.right.dx * 0.008 * settings.joyXSens;
        joy.right.dx=0; joy.right.dy=0;
    }

    // Compute movement vector relative to CAMERA direction
    const fwdX = Math.cos(cameraAngle), fwdY = Math.sin(cameraAngle);
    const rgtX = Math.cos(cameraAngle+Math.PI/2), rgtY = Math.sin(cameraAngle+Math.PI/2);

    let vx = (moveForward-moveBack)*fwdX + (strafeRight-strafeLeft)*rgtX;
    let vy = (moveForward-moveBack)*fwdY + (strafeRight-strafeLeft)*rgtY;
    const vlen=Math.hypot(vx,vy);
    if(vlen>0){ vx/=vlen; vy/=vlen; }

    const speed = (moveForward||moveBack||strafeRight||strafeLeft) ? player.maxSpeed : 0;
    if(speed>0){
        player.speed=Math.min(player.speed+player.accel, speed);
    } else {
        if(player.speed>0) player.speed=Math.max(0,player.speed-player.decel);
        else player.speed=0;
    }

    const moved = tryMove(player.x,player.y, vx*player.speed, vy*player.speed);
    player.x=moved.x; player.y=moved.y;

    // ── Bob ──
    const moving=Math.abs(player.speed)>0.3;
    if(moving){
        bobPhase+=( sprinting?11:6.5)*dt;
        bobOffset=Math.sin(bobPhase)*(sprinting?5:2.5);
    } else { bobPhase*=0.88; bobOffset*=0.88; }

    // Bob applied as canvas transform (with sanity distortion)
    const distortX = sanity.distortion>0.1 ? Math.sin(gameTime*7.3+0.5)*sanity.distortion*8 : 0;
    const distortY = sanity.distortion>0.1 ? Math.cos(gameTime*5.1)*sanity.distortion*6 : 0;
    canvas.style.transform=`translate(${distortX}px,${bobOffset+distortY}px)`;

    // ── Steps ──
    if(moving&&Math.abs(player.speed)>0.4){
        stepTimer-=dt;
        if(stepTimer<=0){
            if(!breathState.holding) playStep(sprinting);
            stepTimer=sprinting?0.27:0.5;
        }
    } else stepTimer=0;

    enemy.hearingRadius = breathState.holding ? 0 : enemy.baseHearingRadius;

    if(breathState.holding){
        breathState.value=Math.max(0, breathState.value-breathState.drain*dt);
        if(breathState.value===0&&!breathState.forcedExhale){
            breathState.forcedExhale=true;
            breathState.holding=false;
            playSample(assetBank.sounds.exhale,0.75,1);
            playBreath(1);
            enemy.state='chase';
            enemy.lastSeenX=player.x; enemy.lastSeenY=player.y;
        }
    } else {
        breathState.value=Math.min(breathState.max, breathState.value+breathState.recover*dt);
        if(breathState.value>breathState.max*0.35) breathState.forcedExhale=false;
    }
    const blurAmt = breathState.holding ? (1.6 + (1-breathState.value/breathState.max)*2.4) : 0;
    document.getElementById('game-container').style.setProperty('--breath-blur', `${blurAmt.toFixed(2)}px`);

    // ── Lantern battery ──
    if(lantern.on){
        lantern.battery=Math.max(0,lantern.battery-lantern.drainRate*dt);
        if(lantern.battery===0){ lantern.on=false; }
    } else {
        // Slow recharge when off
        lantern.battery=Math.min(100, lantern.battery+lantern.rechargeRate*dt);
    }
    updateLanternUI();

    // ── Key pickup proximity prompt ──
    let nearItem=null;
    for(const ki of keyItems){
        if(!ki.collected&&Math.hypot(player.x-ki.wx,player.y-ki.wy)<TILE*1.3){ nearItem=ki; break; }
    }
    const pp=document.getElementById('pickup-prompt');
    if(nearItem){ pp.classList.remove('hidden'); }
    else         { pp.classList.add('hidden'); }

    // ── Switch check ──
    let nearSwitch=null;
    for(const sw of switchItems){
        if(!sw.activated&&Math.hypot(player.x-sw.wx,player.y-sw.wy)<TILE*1.5){ nearSwitch=sw; break; }
    }
    // Reuse pickup text for switch
    if(nearSwitch){
        document.getElementById('pickup-text').innerHTML=`Presiona <strong>F</strong> para activar`;
        pp.classList.remove('hidden');
    } else if(!nearItem){
        document.getElementById('pickup-text').innerHTML=`Presiona <strong>F</strong> para recoger`;
    }

    // ── Door check ──
    const doorPrompt=document.getElementById('door-prompt');
    if(doorPos){
        const ddist=Math.hypot(player.x-doorPos.gx*TILE-TILE/2, player.y-doorPos.gy*TILE-TILE/2);
        if(ddist<TILE*1.4){
            if(objectiveDone){
                // Check key needed
                if(currentObjective.type==='keys'||currentObjective.type==='survive'){
                    if(inventory.keys>0){
                        inventory.keys--; updateInventoryUI();
                        playDoorOpen();
                        doorPrompt.classList.add('hidden');
                        showStoryScreen(); return;
                    } else {
                        doorPrompt.classList.remove('hidden');
                        doorPrompt.textContent='🔒 Necesitas una llave';
                        setTimeout(()=>doorPrompt.classList.add('hidden'),1200);
                    }
                } else {
                    playDoorOpen();
                    doorPrompt.classList.add('hidden');
                    showStoryScreen(); return;
                }
            } else {
                doorPrompt.classList.remove('hidden');
                doorPrompt.textContent='⚠ Completa el objetivo primero';
                setTimeout(()=>doorPrompt.classList.add('hidden'),1800);
            }
        }
    }

    // ── Enemy ──
    updateEnemy(dt);

    // ── Ghosts ──
    updateGhosts(dt);

    // ── Danger ──
    const dx=player.x-enemy.x, dy=player.y-enemy.y;
    const dist=Math.hypot(dx,dy);
    const dangerR=540;
    if(dist<dangerR&&enemy.active){
        dangerLevel=Math.pow(1-dist/dangerR,1.6);
        dangerFlicker+=dt*(3+dangerLevel*8);
        const flick=0.7+Math.sin(dangerFlicker)*0.3;
        document.getElementById('danger-vignette').style.opacity=(dangerLevel*flick*0.92).toString();
        document.getElementById('danger-vignette').classList.remove('hidden');
    } else {
        dangerLevel=0; dangerFlicker=0;
        document.getElementById('danger-vignette').style.opacity='0';
    }

    // ── Flicker events ──
    const flickerActive=horrorEvents.some(e=>e.type==='flicker');
    if(flickerActive){
        const ev=horrorEvents.find(e=>e.type==='flicker');
        ev.data.phase+=dt*18;
        // Rapid flicker
        const flickV=Math.sin(ev.data.phase)*0.5+0.5;
        if(lantern.on) lantern._flickerMult=0.3+flickV*0.7; else lantern._flickerMult=1;
    } else {
        lantern._flickerMult=1;
    }

    // ── Screen shake ──
    if(dist<280&&enemy.active&&enemy.state==='chase'){
        const si=(1-dist/280)*7;
        shakeX=(Math.random()-0.5)*si*2;
        shakeY=(Math.random()-0.5)*si*2;
        document.getElementById('game-container').style.transform=`translate(${shakeX}px,${shakeY}px)`;
    } else {
        shakeX*=0.7; shakeY*=0.7;
        if(Math.abs(shakeX)<0.1) document.getElementById('game-container').style.transform='';
        else document.getElementById('game-container').style.transform=`translate(${shakeX}px,${shakeY}px)`;
    }

    // ── Heartbeat / breath ──
    heartbeatTimer-=dt;
    if(heartbeatTimer<=0&&dangerLevel>0.4){
        playHeartbeat(dangerLevel);
        heartbeatTimer=0.55-dangerLevel*0.22;
    }
    breathTimer-=dt;
    if(breathTimer<=0&&dangerLevel>0.25){
        playBreath(dangerLevel);
        breathTimer=1.8-dangerLevel*0.9;
    }

    // ── Sanity ──
    updateSanity(dt, dist);

    // ── Fear Director ──
    updateFearDirector(dt, dist);

    // ── Horror events ──
    updateHorrorEvents(dt);

    // ── Objective progress ──
    checkObjectiveProgress();

    // ── Death by enemy ──
    if(dist<28&&enemy.active&&!isDying){ startDeath(); }
}

// ═══════════════════════════════════════════
// 12b. OBJECTIVE TRACKING
// ═══════════════════════════════════════════
function checkObjectiveProgress(){
    if(!currentObjective||objectiveDone) return;
    let done=false;
    if(currentObjective.type==='keys'){
        currentObjective.progress=inventory.keys;
        done=inventory.keys>=currentObjective.required;
    } else if(currentObjective.type==='switches'){
        currentObjective.progress=switchItems.filter(s=>s.activated).length;
        done=currentObjective.progress>=currentObjective.required;
    } else if(currentObjective.type==='survive'){
        currentObjective.progress=Math.floor(surviveChaseSecs);
        done=surviveChaseSecs>=currentObjective.required;
    }
    if(done&&!objectiveDone){
        objectiveDone=true;
        playPickup();
        showObjectiveComplete();
    }
    updateObjectiveHUD();
}

function showObjectiveComplete(){
    const el=document.getElementById('obj-complete');
    if(!el) return;
    el.classList.remove('hidden');
    setTimeout(()=>el.classList.add('hidden'),3500);
}

// ═══════════════════════════════════════════
// 13. DEATH ANIMATION
// ═══════════════════════════════════════════
function startDeath(){
    isDying=true; deathTimer=0;
    playDeathSound();
    ensureAudio();
    if(document.pointerLockElement) document.exitPointerLock();
    const ov=document.getElementById('death-overlay');
    ov.classList.remove('hidden','fade');
    ov.classList.add('flash');
    setTimeout(()=>{
        ov.classList.remove('flash');
        ov.classList.add('fade');
        setTimeout(()=>{ triggerGameOver(); },2200);
    },120);
}

// ═══════════════════════════════════════════
// 14. RENDERING
// ═══════════════════════════════════════════
let doorGlowPhase=0;

function render3D(){
    const W=canvas.width, H=canvas.height, HH=H*0.5 + cameraPitch*H*0.22;
    doorGlowPhase+=0.04;

    const ambientLight = lantern.on ? lantern.battery/100*0.18 : 0.018;
    const skyV=Math.floor(ambientLight*18);
    ctx.fillStyle=`rgb(${skyV},${skyV},${Math.floor(skyV*1.6)})`;
    ctx.fillRect(0,0,W,HH);
    ctx.fillStyle=`rgb(${Math.floor(skyV*0.3)},${Math.floor(skyV*0.3)},${Math.floor(skyV*0.3)})`;
    ctx.fillRect(0,HH,W,HH);

    const rayW=W/NRAYS;
    // Lantern radius follows CAMERA angle, not player movement angle
    const baseR=lantern.on ? 260+lantern.battery*2.5 : 80;
    const lightR=baseR*(lantern._flickerMult||1);

    // ── Sanity color distortion ──
    const sanityR = sanity.distortion>0.15 ? Math.floor(sanity.distortion*30) : 0;
    const sanityTint = `rgba(${sanityR*3},0,${sanityR},${sanity.distortion*0.2})`;

    for(let i=0;i<NRAYS;i++){
        // CAMERA-aligned rays
        const rayAngle=cameraAngle - FOV*0.5 + (i/NRAYS)*FOV;
        const cosA=Math.cos(rayAngle), sinA=Math.sin(rayAngle);

        let mapX=Math.floor(player.x/TILE), mapY=Math.floor(player.y/TILE);
        const deltaX=Math.abs(1/(cosA||0.00001)), deltaY=Math.abs(1/(sinA||0.00001));
        let sdX,sdY,stepX,stepY,side=0,tileType=WALL;

        if(cosA<0){ stepX=-1; sdX=(player.x/TILE-mapX)*deltaX; }
        else       { stepX=1;  sdX=(mapX+1-player.x/TILE)*deltaX; }
        if(sinA<0) { stepY=-1; sdY=(player.y/TILE-mapY)*deltaY; }
        else       { stepY=1;  sdY=(mapY+1-player.y/TILE)*deltaY; }

        let hit=false, steps=0;
        while(!hit&&steps++<90){
            if(sdX<sdY){ sdX+=deltaX; mapX+=stepX; side=0; }
            else        { sdY+=deltaY; mapY+=stepY; side=1; }
            if(mapX<0||mapX>=MAPSZ||mapY<0||mapY>=MAPSZ){ hit=true; break; }
            const c=map[mapY][mapX];
            if(c!==FLOOR&&c!==KEY){ hit=true; tileType=c; }
        }

        const perpD=(side===0?(sdX-deltaX):(sdY-deltaY))*TILE;
        zBuffer[i]=perpD;
        const wallH=Math.min(H*6,(TILE*H*CEILING_HEIGHT_FACTOR)/perpD);
        const top=HH-wallH*0.5, bot=HH+wallH*0.5;

        let wx;
        if(side===0) wx=player.y/TILE+(side===0?(sdX-deltaX):0)*sinA;
        else         wx=player.x/TILE+(side===1?(sdY-deltaY):0)*cosA;
        wx-=Math.floor(wx);
        let texX=Math.floor(wx*TEXSZ); if(texX<0)texX=0; if(texX>=TEXSZ)texX=TEXSZ-1;

        const xp=i*rayW;

        if(tileType===DOOR){
            ctx.drawImage(doorTex,texX,0,1,TEXSZ,xp,top,rayW+1,wallH);
            const dg=Math.max(0,1-perpD/500)*(0.2+Math.sin(doorGlowPhase)*0.12);
            ctx.fillStyle=`rgba(255,200,30,${dg})`;
            ctx.fillRect(xp,top,rayW+1,wallH);
        } else if(tileType===SWITCH_TILE){
            ctx.drawImage(switchTex,texX,0,1,TEXSZ,xp,top,rayW+1,wallH);
            const sg=Math.max(0,1-perpD/400)*(0.3+Math.sin(doorGlowPhase*1.4)*0.15);
            ctx.fillStyle=`rgba(0,180,255,${sg})`;
            ctx.fillRect(xp,top,rayW+1,wallH);
        } else {
            ctx.drawImage(wallTex,texX,0,1,TEXSZ,xp,top,rayW+1,wallH);
            if(((mapX*19 + mapY*13)%17===0) && Math.random()<0.012){
                ctx.fillStyle='rgba(120,0,0,0.35)';
                ctx.fillRect(xp,top+wallH*0.55,rayW+1,wallH*0.4);
            }
        }

        // ── Smooth volumetric fog (no pixelation) ──
        // We use a SMOOTH gradient overlay, not per-strip rectangles for fog
        // Lamp light from ceiling fixtures
        let lampBoost=0;
        const hitX=player.x+cosA*perpD, hitY=player.y+sinA*perpD;
        for(const lamp of lampSources){
            const ld=Math.hypot(hitX-lamp.x, hitY-lamp.y);
            if(ld<360){
                const flick=lamp.flicker?(0.45+Math.abs(Math.sin(gameTime*7+lamp.phase))*0.55):1;
                lampBoost += Math.max(0,1-ld/360)*0.26*lamp.intensity*flick;
            }
        }
        if(lampBoost>0.02){
            ctx.fillStyle=`rgba(255,240,190,${Math.min(0.32,lampBoost)})`;
            ctx.fillRect(xp,top,rayW+1,wallH);
        }

        const fog=Math.min(0.98,perpD/lightR);
        ctx.fillStyle=`rgba(0,0,0,${fog})`;
        ctx.fillRect(xp,top,rayW+1,wallH);

        if(side===1){ ctx.fillStyle='rgba(0,0,0,0.2)'; ctx.fillRect(xp,top,rayW+1,wallH); }

        if(lantern.on&&perpD<lightR){
            const flickerM=lantern._flickerMult||1;
            const conePos=Math.abs(i/NRAYS-0.5)*2;
            const li=Math.pow(1-perpD/lightR,1.5)*(0.5+conePos*0)*0.28*(lantern.battery/100)*flickerM;
            const coneBoost=(1-conePos)*0.15;
            ctx.fillStyle=`rgba(255,165,40,${li+coneBoost})`;
            ctx.fillRect(xp,top,rayW+1,wallH);
        }

        // ── Smooth red fog — distance-based gradient, no pixelation ──
        if(dangerLevel>0.05){
            const flick=0.6+Math.sin(dangerFlicker+i*0.04)*0.4;
            // Use smooth exponential falloff based on depth
            const rf=dangerLevel*Math.pow(1-Math.min(1,perpD/600),0.8)*0.8*flick;
            ctx.fillStyle=`rgba(160,0,0,${rf})`;
            ctx.fillRect(xp,top,rayW+1,wallH);
        }

        // Sanity tint
        if(sanity.distortion>0.1){
            ctx.fillStyle=sanityTint;
            ctx.fillRect(xp,top,rayW+1,wallH);
        }
    }

    // ── Smooth floor/ceiling fog overlay ──
    // Gradient fog bands at top and bottom for smooth look
    const fgTop=ctx.createLinearGradient(0,0,0,HH*0.6);
    fgTop.addColorStop(0,`rgba(0,0,0,${0.85-ambientLight*2})`);
    fgTop.addColorStop(1,'rgba(0,0,0,0)');
    ctx.fillStyle=fgTop; ctx.fillRect(0,0,W,HH);

    const fgBot=ctx.createLinearGradient(0,H,0,HH*1.4);
    fgBot.addColorStop(0,`rgba(0,0,0,${0.9-ambientLight*2})`);
    fgBot.addColorStop(1,'rgba(0,0,0,0)');
    ctx.fillStyle=fgBot; ctx.fillRect(0,HH,W,HH);

    // ── Danger fog overlay (smooth radial, not per-ray) ──
    if(dangerLevel>0.08){
        const flick2=0.7+Math.sin(dangerFlicker*0.7)*0.3;
        const rg=ctx.createRadialGradient(W*0.5,H*0.5,H*0.1,W*0.5,H*0.5,H*0.75);
        rg.addColorStop(0,'rgba(120,0,0,0)');
        rg.addColorStop(0.6,`rgba(140,0,0,${dangerLevel*0.25*flick2})`);
        rg.addColorStop(1,`rgba(160,0,0,${dangerLevel*0.65*flick2})`);
        ctx.fillStyle=rg;
        ctx.fillRect(0,0,W,H);
    }

    renderKeys();
    renderGhosts();
    renderEnemySprite();
    renderSanityOverlay();
}

// ── Sanity visual overlay ──
function renderSanityOverlay(){
    if(sanity.distortion<0.1) return;
    const W=canvas.width, H=canvas.height;
    const d=sanity.distortion;
    // Chromatic aberration simulation — tinted borders
    if(d>0.2){
        ctx.fillStyle=`rgba(255,0,0,${d*0.06})`;
        ctx.fillRect(0,0,W,H);
        // Edge vignette tint
        const rv=ctx.createRadialGradient(W/2,H/2,H*0.2,W/2,H/2,H*0.8);
        rv.addColorStop(0,'rgba(0,0,0,0)');
        rv.addColorStop(1,`rgba(80,0,60,${d*0.5})`);
        ctx.fillStyle=rv; ctx.fillRect(0,0,W,H);
    }
    // False HUD element — a second ghost crosshair
    if(d>0.4){
        const offX=(Math.random()-0.5)*d*60, offY=(Math.random()-0.5)*d*40;
        ctx.fillStyle=`rgba(255,0,0,${d*0.3})`;
        ctx.font=`${1.6}rem monospace`;
        ctx.textAlign='center';
        ctx.fillText('·',W/2+offX,H/2+offY);
    }
}

function renderKeys(){
    const W=canvas.width, H=canvas.height;
    const now=Date.now();
    for(const ki of keyItems){
        if(ki.collected) continue;
        const dx=ki.wx-player.x, dy=ki.wy-player.y;
        let sa=Math.atan2(dy,dx)-cameraAngle;
        while(sa<-Math.PI) sa+=Math.PI*2;
        while(sa>Math.PI)  sa-=Math.PI*2;
        const dist=Math.hypot(dx,dy);
        if(Math.abs(sa)>FOV*0.6||dist>500||dist<10) continue;
        const screenX=(sa/(FOV*0.5)+1)*0.5*W;
        const sprW=Math.min(W*0.3,(TILE*W*0.55)/dist);
        const sprH=sprW*0.5;
        const startX=screenX-sprW*0.5;
        const yPos=H*0.5+wallHeightAtRay(sa)*(0.45);
        const rayW2=W/NRAYS;
        const vis=Math.max(0,1-dist/(lantern.on?420:160));
        if(vis<0.04) continue;
        const glow=0.75+Math.sin(now*0.004)*0.25;
        for(let sx=0;sx<sprW;sx++){
            const scx=Math.floor(startX+sx);
            const ri=Math.floor(scx/rayW2);
            if(ri<0||ri>=NRAYS||dist>=zBuffer[ri]) continue;
            const tx=Math.floor((sx/sprW)*64);
            ctx.globalAlpha=vis*glow;
            ctx.drawImage(keySpriteTex,tx,0,1,32,scx,yPos-sprH,1,sprH);
            ctx.globalAlpha=1;
        }
        if(vis>0.15){
            ctx.beginPath();
            ctx.arc(screenX,yPos-sprH*0.5,Math.max(3,sprW*0.1*vis*glow),0,Math.PI*2);
            ctx.fillStyle=`rgba(255,215,0,${vis*0.4*glow})`;
            ctx.fill();
        }
    }
}

function wallHeightAtRay(sprAngle){
    return canvas.height*0.06;
}

// ── Ghost rendering ──
function renderGhosts(){
    const W=canvas.width, H=canvas.height;
    for(const g of ghosts){
        if(g.opacity<0.01) continue;
        const dx=g.x-player.x, dy=g.y-player.y;
        let sa=Math.atan2(dy,dx)-cameraAngle;
        while(sa<-Math.PI) sa+=Math.PI*2;
        while(sa>Math.PI)  sa-=Math.PI*2;
        const dist=Math.hypot(dx,dy);
        if(Math.abs(sa)>FOV*0.65||dist>600||dist<10) continue;
        const screenX=(sa/(FOV*0.5)+1)*0.5*W;
        const sprH=Math.min(H*1.8,(TILE*H*1.0)/dist);
        const sprW=sprH*0.5;
        const startX=screenX-sprW*0.5;
        const rayW=W/NRAYS;

        for(let sx=0;sx<sprW;sx++){
            const scx=Math.floor(startX+sx);
            const ri=Math.floor(scx/rayW);
            if(ri<0||ri>=NRAYS||dist>=zBuffer[ri]) continue;
            const tx=Math.floor((sx/sprW)*96);
            ctx.globalAlpha=g.opacity*0.45;
            ctx.drawImage(enemyTex,tx,0,1,192,scx,H*0.5-sprH*0.5,1,sprH);
            ctx.globalAlpha=1;
        }

        // Ghost glow — bluish
        if(g.opacity>0.2){
            const grd=ctx.createRadialGradient(screenX,H*0.5,2,screenX,H*0.5,sprW*0.6);
            grd.addColorStop(0,`rgba(100,100,255,${g.opacity*0.15})`);
            grd.addColorStop(1,'rgba(100,100,255,0)');
            ctx.fillStyle=grd;
            ctx.fillRect(screenX-sprW,H*0.5-sprH*0.6,sprW*2,sprH);
        }
    }
}

function renderEnemySprite(){
    if(!enemy.active) return;
    const W=canvas.width, H=canvas.height;
    const dx=enemy.x-player.x, dy=enemy.y-player.y;
    let sa=Math.atan2(dy,dx)-cameraAngle;
    while(sa<-Math.PI) sa+=Math.PI*2;
    while(sa>Math.PI)  sa-=Math.PI*2;
    const dist=Math.hypot(dx,dy);
    if(Math.abs(sa)>FOV*0.62||dist>900||dist<12) return;

    const screenX=(sa/(FOV*0.5)+1)*0.5*W;
    const sprH=Math.min(H*2.2,(TILE*H*1.25)/dist);
    const sprW=sprH*0.5;
    const startX=screenX-sprW*0.5;
    const rayW=W/NRAYS;

    const maxVis=lantern.on?680:180;
    const vis=Math.max(0,1-dist/maxVis);
    if(vis<0.04) return;

    const darkOverlay=1-vis;

    for(let sx=0;sx<sprW;sx++){
        const scx=Math.floor(startX+sx);
        const ri=Math.floor(scx/rayW);
        if(ri<0||ri>=NRAYS||dist>=zBuffer[ri]) continue;
        const tx=Math.floor((sx/sprW)*96);
        ctx.globalAlpha=vis;
        ctx.drawImage(enemyTex,tx,0,1,192,scx,H*0.5-sprH*0.5,1,sprH);
        ctx.globalAlpha=1;
        if(darkOverlay>0.05){
            ctx.fillStyle=`rgba(0,0,0,${darkOverlay*0.82})`;
            ctx.fillRect(scx,H*0.5-sprH*0.5,1,sprH);
        }
    }

    // Black smoke around enemy
    const smokeCount=6;
    for(let i=0;i<smokeCount;i++){
        const t=gameTime*1.2+i*0.7;
        const sx=screenX+Math.sin(t*1.7+i)*sprW*0.2;
        const sy=H*0.5+sprH*0.1-Math.abs(Math.sin(t))*sprH*0.35;
        const sr=Math.max(10,sprW*0.18+i*2);
        const sg=ctx.createRadialGradient(sx,sy,2,sx,sy,sr);
        sg.addColorStop(0,'rgba(20,20,20,0.45)');
        sg.addColorStop(1,'rgba(0,0,0,0)');
        ctx.fillStyle=sg;
        ctx.beginPath(); ctx.arc(sx,sy,sr,0,Math.PI*2); ctx.fill();
    }

    if(dist<400){
        const eyeVis=Math.max(0,1-dist/400);
        const eyeY=H*0.5-sprH*0.36;
        const es=Math.max(1.5,sprH*0.035*eyeVis);
        const eyeL=screenX-sprW*0.16, eyeR=screenX+sprW*0.16;
        ctx.beginPath(); ctx.arc(eyeL,eyeY,es*2.5,0,Math.PI*2);
        ctx.fillStyle=`rgba(180,0,0,${eyeVis*0.25})`; ctx.fill();
        ctx.beginPath(); ctx.arc(eyeR,eyeY,es*2.5,0,Math.PI*2);
        ctx.fillStyle=`rgba(180,0,0,${eyeVis*0.25})`; ctx.fill();
        ctx.beginPath(); ctx.arc(eyeL,eyeY,es,0,Math.PI*2);
        ctx.arc(eyeR,eyeY,es,0,Math.PI*2);
        ctx.fillStyle=`rgba(255,30,30,${eyeVis*0.95})`; ctx.fill();
        ctx.beginPath(); ctx.arc(eyeL-es*0.25,eyeY-es*0.25,es*0.35,0,Math.PI*2);
        ctx.arc(eyeR-es*0.25,eyeY-es*0.25,es*0.35,0,Math.PI*2);
        ctx.fillStyle=`rgba(255,200,200,${eyeVis*0.5})`; ctx.fill();
        if(enemy.state==='chase'&&vis>0.2){
            const auraR=sprW*0.7;
            const ag=ctx.createRadialGradient(screenX,eyeY,0,screenX,eyeY,auraR);
            ag.addColorStop(0,`rgba(100,0,0,${vis*0.15})`);
            ag.addColorStop(1,'rgba(100,0,0,0)');
            ctx.fillStyle=ag;
            ctx.fillRect(screenX-auraR,H*0.5-sprH*0.6,auraR*2,sprH*0.5);
        }
    }
}

// ═══════════════════════════════════════════
// 15. GAME LOOP
// ═══════════════════════════════════════════
function gameLoop(ts){
    if(!isRunning) return;
    if(isPaused){ lastTime=ts; requestAnimationFrame(gameLoop); return; }
    if(!lastTime) lastTime=ts;
    const dt=Math.min((ts-lastTime)/1000,0.05);
    lastTime=ts; gameTime+=dt;

    if(!isDying) updateLogic(dt);
    render3D();
    requestAnimationFrame(gameLoop);
}

function resize(){
    canvas.width=window.innerWidth;
    canvas.height=window.innerHeight;
    ctx.imageSmoothingEnabled=false;
}
window.addEventListener('resize',resize);

// ═══════════════════════════════════════════
// 16. STORY SCREENS BETWEEN LEVELS
// ═══════════════════════════════════════════

function maybeShowCreepypasta(){
    if(Math.random()>0.5) return;
    const lines=[
        'JEFF THE KILLER TE MIRA DESDE LA NIEBLA',
        'SLENDERMAN YA CONOCE TU RUTA',
        'SMILE DOG SUSURRA EN LAS PAREDES',
        'BEN DROWNED TE ESPERA EN EL SIGUIENTE PASILLO',
    ];
    showWhisperText(lines[Math.floor(Math.random()*lines.length)]);
}

const STORY_TEXTS = [
    null, // level 1 has no intro (covered by start screen)
    {
        title: 'EL LABERINTO RESPIRA',
        body:  'Algo se mueve entre las sombras. La niebla se densifica. No eras el primero... ni serás el último.',
        hint:  '⚠ El monstruo ahora recuerda tu olor.'
    },
    {
        title: 'LAS PAREDES SANGRAN',
        body:  'Escuchas voces que no existen. O quizás sí. La cordura es un lujo aquí abajo.',
        hint:  '⚠ Los interruptores encierran la salida. Búscalos.'
    },
    {
        title: 'SIN RETORNO',
        body:  'El laberinto cambia. Pasillos que recuerdas ya no están. Sientes una presencia detrás de ti... siempre.',
        hint:  '⚠ Cuida tu cordura. Lo que ves puede no ser real.'
    },
    {
        title: 'LA OSCURIDAD COMPLETA',
        body:  'Tu linterna ya no es suficiente. Hay cosas que la luz no puede ahuyentar.',
        hint:  '⚠ Sobrevive. Eso es todo lo que queda.'
    },
];

function showStoryScreen(){
    storyScreenActive=true;
    isPaused=true;
    if(document.pointerLockElement) document.exitPointerLock();

    const idx=Math.min(level, STORY_TEXTS.length-1);
    const story=STORY_TEXTS[idx];

    const ss=document.getElementById('story-screen');
    if(!ss){ advanceLevel(); return; }

    if(story){
        document.getElementById('story-title').textContent=story.title;
        document.getElementById('story-body').textContent=story.body;
        document.getElementById('story-hint').textContent=story.hint||'';
        ss.classList.remove('hidden');
    } else {
        advanceLevel();
    }
}

function advanceLevel(){
    storyScreenActive=false;
    isPaused=false;
    score+=1000+level*250;
    level++;
    sanity.value=Math.min(100,sanity.value+25);
    lantern.battery=Math.min(100,lantern.battery+30);
    surviveChaseSecs=0;
    document.getElementById('ui-level').textContent=level;
    document.getElementById('ui-score').textContent=score;
    dangerLevel=0; dangerFlicker=0;
    document.getElementById('danger-vignette').style.opacity='0';
    whisperTimer=12+Math.random()*15;
    ghosts=[];
    inventory.keys=0; updateInventoryUI();
    fearDirector.tension=0;
    fearDirector.eventCooldown=5;
    generateDungeon();
    maybeShowCreepypasta();
    if(!isMobile) canvas.requestPointerLock();
}

// ═══════════════════════════════════════════
// 17. INIT / TRANSITIONS
// ═══════════════════════════════════════════
function initGame(){
    ensureAudio();
    level=1; score=0; dangerLevel=0; dangerFlicker=0; isDying=false;
    inventory.keys=0; lantern.battery=100; lantern.on=false;
    bobPhase=0; bobOffset=0; gameTime=0;
    sanity.value=100; sanity.distortion=0;
    cameraPitch=0;
    breathState.value=breathState.max;
    breathState.holding=false;
    breathState.forcedExhale=false;
    fearDirector.tension=0; fearDirector.eventCooldown=8;
    fearDirector.silenceActive=false;
    horrorEvents=[];
    ghosts=[];
    whisperTimer=15+Math.random()*10;
    surviveChaseSecs=0;

    document.getElementById('ui-level').textContent=level;
    document.getElementById('ui-score').textContent=score;
    // Remove time display
    const timeEl=document.getElementById('ui-time');
    if(timeEl){
        const timeStat=timeEl.closest('.hud-stat');
        if(timeStat) timeStat.style.display='none';
    }
    document.getElementById('danger-vignette').style.opacity='0';
    document.getElementById('death-overlay').classList.add('hidden');
    document.getElementById('death-overlay').classList.remove('flash','fade');
    updateInventoryUI(); updateLanternUI();

    generateDungeon(); resize();
    isRunning=true; isPaused=false; lastTime=0;
    requestAnimationFrame(gameLoop);
    if(!isMobile) canvas.requestPointerLock();
}

function triggerGameOver(){
    isRunning=false; isDying=false;
    document.getElementById('danger-vignette').style.opacity='0.85';
    document.getElementById('game-over').classList.remove('hidden');
    document.getElementById('final-stats').textContent=`Nivel alcanzado: ${level}  |  Puntos: ${score}`;
}

function togglePause(){
    if(!isRunning) return;
    isPaused=!isPaused;
    const ps=document.getElementById('pause-screen');
    if(isPaused){
        ps.classList.remove('hidden');
        if(document.pointerLockElement) document.exitPointerLock();
    } else {
        ps.classList.add('hidden');
        if(!isMobile) canvas.requestPointerLock();
    }
}

// ── Objective HUD ──
function updateObjectiveHUD(){
    if(!currentObjective) return;
    const el=document.getElementById('ui-objective');
    const prog=document.getElementById('ui-obj-progress');
    if(!el) return;
    el.textContent=currentObjective.label||'';
    if(prog){
        if(currentObjective.type==='survive'){
            prog.textContent=`${Math.floor(currentObjective.progress||0)}/${currentObjective.required}s`;
        } else if(currentObjective.required>1){
            prog.textContent=`${currentObjective.progress||0}/${currentObjective.required}`;
        } else {
            prog.textContent=objectiveDone?'✓':'';
        }
    }
    if(el.parentElement) el.parentElement.classList.toggle('obj-done',objectiveDone);
}

function updateInventoryUI(){
    document.getElementById('key-count').textContent=inventory.keys;
    document.getElementById('slot-key').classList.toggle('has-item',inventory.keys>0);
}
function updateLanternUI(){
    const panel=document.querySelector('.lantern-panel');
    const bar=document.getElementById('battery-bar');
    const pct=document.getElementById('battery-pct');
    bar.style.width=lantern.battery+'%';
    pct.textContent=Math.ceil(lantern.battery)+'%';
    bar.classList.toggle('low',lantern.battery<20);
    if(panel) panel.classList.toggle('active',lantern.on);
    const oxy=document.getElementById('oxygen-bar');
    if(oxy){
        const p=Math.max(0,Math.min(100,(breathState.value/breathState.max)*100));
        oxy.style.background=`linear-gradient(90deg,#5fd6ff ${p}%, rgba(60,20,20,0.9) ${p}%)`;
    }
}

function toggleLantern(){
    if(lantern.battery<=0) return;
    lantern.on=!lantern.on; updateLanternUI();
}

function tryPickup(){
    // Try switch first
    for(const sw of switchItems){
        if(!sw.activated&&Math.hypot(player.x-sw.wx,player.y-sw.wy)<TILE*1.5){
            sw.activated=true;
            map[sw.gy][sw.gx]=WALL; // deactivate tile
            playSwitchActivate();
            checkObjectiveProgress();
            document.getElementById('pickup-prompt').classList.add('hidden');
            return;
        }
    }
    // Try key
    for(const ki of keyItems){
        if(!ki.collected&&Math.hypot(player.x-ki.wx,player.y-ki.wy)<TILE*1.4){
            ki.collected=true; map[ki.gy][ki.gx]=FLOOR;
            inventory.keys++; updateInventoryUI(); playPickup();
            document.getElementById('pickup-prompt').classList.add('hidden');
            checkObjectiveProgress();
            break;
        }
    }
}

// ═══════════════════════════════════════════
// 18. SETTINGS PANEL
// ═══════════════════════════════════════════
document.querySelectorAll('.tab-btn').forEach(btn=>{
    btn.addEventListener('click',()=>{
        document.querySelectorAll('.tab-btn').forEach(b=>b.classList.remove('active'));
        document.querySelectorAll('.tab-panel').forEach(p=>p.classList.add('hidden'));
        btn.classList.add('active');
        document.getElementById(btn.dataset.tab).classList.remove('hidden');
    });
});
['x','y','mouse'].forEach(axis=>{
    const sl=document.getElementById(`sens-${axis}`);
    const vl=document.getElementById(`sens-${axis}-val`);
    if(sl) sl.addEventListener('input',()=>{ vl.textContent=parseFloat(sl.value).toFixed(1); });
});

let listeningFor=null;
document.querySelectorAll('.keybind-btn').forEach(btn=>{
    btn.addEventListener('click',()=>{
        if(listeningFor){ document.getElementById(`keybind-${listeningFor}`).classList.remove('listening'); }
        listeningFor=btn.dataset.action;
        btn.classList.add('listening');
        btn.textContent='...';
    });
});
window.addEventListener('keydown',e=>{
    if(!listeningFor) return;
    e.preventDefault();
    const action=listeningFor; listeningFor=null;
    const btn=document.getElementById(`keybind-${action}`);
    btn.classList.remove('listening');
    let label=e.code.replace('Key','').replace('Left','').replace('Right','');
    if(e.code.startsWith('Shift')) label='SHIFT';
    btn.textContent=label;
    if(action==='lantern') settings.keys.lantern=e.code;
    if(action==='sprint')  settings.keys.sprint=e.code;
    if(action==='pickup')  settings.keys.pickup=e.code;
});

document.getElementById('save-settings-btn').addEventListener('click',()=>{
    settings.mouseSens=parseFloat(document.getElementById('sens-mouse').value)*0.0022;
    settings.joyXSens=parseFloat(document.getElementById('sens-x').value);
    settings.joyYSens=parseFloat(document.getElementById('sens-y').value);
    document.querySelectorAll('.tab-btn').forEach(b=>b.classList.remove('active'));
    document.querySelectorAll('.tab-panel').forEach(p=>p.classList.add('hidden'));
    document.querySelector('[data-tab="tab-resume"]').classList.add('active');
    document.getElementById('tab-resume').classList.remove('hidden');
});

// ═══════════════════════════════════════════
// 19. BUTTONS & MOBILE INIT
// ═══════════════════════════════════════════
preloadRealismAssets();

document.getElementById('start-btn').addEventListener('click',()=>{
    ensureAudio();
    document.getElementById('start-screen').classList.add('hidden');
    document.getElementById('hud').classList.remove('hidden');
    document.getElementById('crosshair').classList.remove('hidden');
    if(isMobile){ document.getElementById('mobile-controls').classList.remove('hidden'); }
    initGame();
});
document.getElementById('restart-btn').addEventListener('click',()=>{
    ensureAudio();
    document.getElementById('game-over').classList.add('hidden');
    document.getElementById('hud').classList.remove('hidden');
    document.getElementById('crosshair').classList.remove('hidden');
    if(isMobile){ document.getElementById('mobile-controls').classList.remove('hidden'); }
    initGame();
});
document.getElementById('resume-btn').addEventListener('click',togglePause);

document.getElementById('start-btn').addEventListener('touchstart',e=>{ e.preventDefault(); document.getElementById('start-btn').click(); },{passive:false});
document.getElementById('restart-btn').addEventListener('touchstart',e=>{ e.preventDefault(); document.getElementById('restart-btn').click(); },{passive:false});
document.getElementById('resume-btn').addEventListener('touchstart',e=>{ e.preventDefault(); togglePause(); },{passive:false});

// Story screen continue button
const storyContinue=document.getElementById('story-continue-btn');
if(storyContinue){
    storyContinue.addEventListener('click',()=>{
        document.getElementById('story-screen').classList.add('hidden');
        advanceLevel();
    });
    storyContinue.addEventListener('touchstart',e=>{
        e.preventDefault(); storyContinue.click();
    },{passive:false});
}


function goToStartMenu(){
    isRunning=false;
    isPaused=false;
    if(document.pointerLockElement) document.exitPointerLock();
    document.getElementById('pause-screen').classList.add('hidden');
    document.getElementById('game-over').classList.add('hidden');
    document.getElementById('hud').classList.add('hidden');
    document.getElementById('crosshair').classList.add('hidden');
    document.getElementById('start-screen').classList.remove('hidden');
}

function rerollRun(){
    document.getElementById('pause-screen').classList.add('hidden');
    document.getElementById('game-over').classList.add('hidden');
    initGame();
}

document.getElementById('pause-home-btn')?.addEventListener('click',goToStartMenu);
document.getElementById('gameover-home-btn')?.addEventListener('click',goToStartMenu);
document.getElementById('pause-reroll-btn')?.addEventListener('click',rerollRun);
document.getElementById('gameover-reroll-btn')?.addEventListener('click',rerollRun);
