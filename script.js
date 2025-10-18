/* GoldDigger - single-file main logic
   - Implements required functions:
     initGame(), generateWorld(seed), camera.update(), mineBlock(x,y),
     sellAll(), openShop(), closeShop(), buyUpgrade(upgradeId),
     saveGame(), loadGame(), updateUI()
   - Uses layered canvases, localStorage save, and modular objects.
*/

/* ============ Constants & Utils ============ */
const TILE_SIZE = 16; // pixel tile size (retro)
const VIEW_TILES_X = 26; // viewport in tiles (approx)
const VIEW_TILES_Y = 26;
const WORLD_DEPTH_TILES = 2000; // deep world
const CHUNK_HEIGHT = 32; // generate chunks of vertical tiles
const SAVE_KEY = 'gold_digger_save_v1';

const TILE_TYPES = [
  {id: 'dirt', color:'#6b4f2b', value:1, hp:1},
  {id: 'coal', color:'#262626', value:5, hp:2},
  {id: 'iron', color:'#7f7f7f', value:10, hp:3},
  {id: 'gold', color:'#ffcf32', value:25, hp:4},
  {id: 'diamond', color:'#7fe7ff', value:50, hp:6}
];

// deterministic PRNG from seed
function makeRng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6D2B79F5) | 0;
    let t = Math.imul(s ^ s >>> 15, 1 | s);
    t = (t + Math.imul(t ^ t >>> 7, 61 | t)) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}

function clamp(a,min,max){return Math.max(min,Math.min(max,a))}
function lerp(a,b,t){return a + (b-a)*t}

/* ============ DOM & Canvas refs ============ */
const canvases = {
  bg: document.getElementById('bg-canvas'),
  px: document.getElementById('parallax-canvas'),
  tiles: document.getElementById('tile-canvas'),
  ent: document.getElementById('entity-canvas'),
  light: document.getElementById('light-canvas')
};
const ctx = {
  bg: canvases.bg.getContext('2d'),
  px: canvases.px.getContext('2d'),
  tiles: canvases.tiles.getContext('2d'),
  ent: canvases.ent.getContext('2d'),
  light: canvases.light.getContext('2d')
};
const UI = {
  root: document.getElementById('game-root'),
  loading: document.getElementById('loading-screen'),
  continueBtn: document.getElementById('continue-btn'),
  money: document.getElementById('money'),
  depth: document.getElementById('depth'),
  energy: document.getElementById('energy'),
  inventoryList: document.getElementById('inventory-list'),
  backpackInfo: document.getElementById('backpack-info'),
  shopBtn: document.getElementById('shop-btn'),
  sellBtn: document.getElementById('sell-btn'),
  shop: document.getElementById('shop'),
  shopItems: document.getElementById('shop-items'),
  closeShop: document.getElementById('close-shop'),
  muteBtn: document.getElementById('mute-btn'),
  fxLayer: document.getElementById('fx-layer'),
  motionToggle: document.getElementById('motion-toggle'),
  mobileControls: document.getElementById('mobile-controls'),
  leftBtn: document.getElementById('left-btn'),
  rightBtn: document.getElementById('right-btn'),
  downBtn: document.getElementById('down-btn'),
  mineBtn: document.getElementById('mine-btn')
};

/* set canvas sizes to window */
function resizeCanvases(){
  const w = innerWidth, h = innerHeight;
  for (let c of Object.values(canvases)){
    c.width = w; c.height = h;
  }
}
window.addEventListener('resize', resizeCanvases);

/* ============ Audio placeholders ============ */
const audio = {
  enabled: true,
  sfx: {},
  play(name){
    if(!this.enabled) return;
    const a = this.sfx[name];
    if(!a) return;
    try{ a.currentTime = 0; a.play(); }catch(e){}
  },
  toggle(){ this.enabled = !this.enabled; localState.mute = !this.enabled; saveGame(); updateUI(); }
};

/* Create tiny placeholder audio using base64 silent beep or use <audio> preloads */
function loadAudioPlaceholders(){
  // small beep placeholder using WebAudio if available
  try {
    const ctxA = new (window.AudioContext || window.webkitAudioContext)();
    ['hit','break','sell','buy','click'].forEach((name,i)=>{
      // create short oscillator buffer
      const dur = 0.08;
      const sr = ctxA.sampleRate;
      const buf = ctxA.createBuffer(1, sr * dur, sr);
      const data = buf.getChannelData(0);
      for(let j=0;j<data.length;j++){
        data[j] = Math.tanh(Math.sin(j/ (sr/dur) * (400 + i*60 )) * 0.6) * (1 - j/data.length);
      }
      const node = ctxA.createBufferSource();
      node.buffer = buf;
      const dest = ctxA.createGain();
      dest.gain.value = 0.04;
      node.connect(dest); dest.connect(ctxA.destination);
      audio.sfx[name] = {
        play(){
          const n = ctxA.createBufferSource();
          n.buffer = buf;
          const g = ctxA.createGain();
          g.gain.value = 0.04;
          n.connect(g); g.connect(ctxA.destination);
          n.start();
        }
      }
    });
  } catch(e){
    // fallback: no audio
    console.warn('AudioContext not available, skipping audio placeholders.');
  }
}

/* ============ Game State ============ */
let localState = {
  money: 0,
  depthTile: 0, // player tile y depth; surface at 0 (y increases downward)
  inventory: {dirt:0, coal:0, iron:0, gold:0, diamond:0},
  backpackSize: 10,
  pickaxeLevel: 0,
  lightRadius: 120,
  energy: 100,
  upgrades: {}, // purchased upgrades by id
  seed: Math.floor(Math.random()*1e9),
  mute: false
};

/* Minimal change-tracking for UI to reduce DOM writes */
const uiCache = {money: null, depth: null, energy: null, invJSON: null, backpackSize:null};

/* ============ World / Chunk system ============ */
const World = {
  seed: null,
  rng: null,
  // store chunks by index (chunk 0 starts at surface going down positive)
  chunks: new Map(),
  getChunkIndexForTileY(tileY){ return Math.floor(tileY / CHUNK_HEIGHT); },

  init(seed){
    this.seed = seed;
    this.rng = makeRng(seed);
    this.chunks.clear();
  },

  // deterministic chunk generation
  generateChunk(index){
    if(this.chunks.has(index)) return this.chunks.get(index);
    const rng = makeRng(this.seed + index * 7919);
    const tiles = new Array(CHUNK_HEIGHT);
    for(let y=0;y<CHUNK_HEIGHT;y++){
      tiles[y] = new Array(64); // width larger than needed; world width is effectively infinite horizontally but we will generate on demand via simple algo
      for(let x=0;x<64;x++){
        const globalY = index*CHUNK_HEIGHT + y;
        // depth bias
        const depthBand = Math.floor(globalY / 200);
        // base probabilities: dirt dominant near surface; rarer ores deeper
        const roll = rng();
        let t = 'dirt';
        // ramp ores probability with depth
        if(roll > 0.98 - depthBand*0.002) t = 'diamond';
        else if(roll > 0.94 - depthBand*0.004) t = 'gold';
        else if(roll > 0.85 - depthBand*0.01) t = 'iron';
        else if(roll > 0.7 - depthBand*0.02) t = 'coal';
        tiles[y][x] = {type:t, hp: TILE_TYPES.find(tt=>tt.id===t).hp};
      }
    }
    this.chunks.set(index, tiles);
    return tiles;
  },

  getTile(tileX,tileY){
    if(tileY < 0) return {type:'air', hp:0};
    if(tileY > WORLD_DEPTH_TILES) return {type:'bedrock', hp:9999};
    const chunkIdx = this.getChunkIndexForTileY(tileY);
    const chunk = this.generateChunk(chunkIdx);
    const localY = tileY - chunkIdx * CHUNK_HEIGHT;
    const localX = ((tileX % 64) + 64) % 64;
    return chunk[localY][localX];
  },

  setTile(tileX,tileY, tile){
    const chunkIdx = this.getChunkIndexForTileY(tileY);
    const chunk = this.generateChunk(chunkIdx);
    const localY = tileY - chunkIdx * CHUNK_HEIGHT;
    const localX = ((tileX % 64) + 64) % 64;
    chunk[localY][localX] = tile;
  }
};

/* ============ Player ============ */
const Player = {
  x: 32, y: 0, // tile-space coords (floating)
  px: 32 * TILE_SIZE, py: 0,
  speed: 3, // tiles per second horizontally
  width: TILE_SIZE, height: TILE_SIZE*1.5,
  velocity: {x:0,y:0},
  mining: {target:null, progress:0, lastSwing:0},

  update(dt, input){
    // horizontal movement
    const move = (input.left?-1:0) + (input.right?1:0);
    this.x += move * this.speed * dt;
    // clamp x to some sane range
    this.x = clamp(this.x, -1024, 1024);
    // vertical (down) moves (player "descends" smoothly)
    if(input.down){
      this.y += this.speed * dt;
      this.y = clamp(this.y, 0, WORLD_DEPTH_TILES-1);
    }
    // tile position to pixel pos
    this.px = this.x * TILE_SIZE;
    this.py = this.y * TILE_SIZE;

    // mining process (progress per second based on pickaxe level)
    if(input.mine && this.mining.target){
      const target = this.mining.target;
      const tile = World.getTile(target.x, target.y);
      if(tile.type === 'air'){ this.mining.target = null; this.mining.progress = 0; return; }
      const pickLevel = localState.pickaxeLevel;
      const speedMultiplier = 1 + pickLevel * 0.5;
      const amountPerSec = speedMultiplier;
      this.mining.progress += amountPerSec * dt;
      // show particle lightly when swinging
      if(Date.now() - this.mining.lastSwing > 120){
        spawnParticles(this.px + TILE_SIZE/2, this.py + TILE_SIZE/2, 6);
        this.mining.lastSwing = Date.now();
        audio.play('hit');
      }
      if(this.mining.progress >= tile.hp){
        mineBlock(target.x, target.y);
        this.mining.progress = 0;
        this.mining.target = null;
      }
    } else {
      this.mining.progress = 0;
    }

    // energy drain when underground
    const atSurface = this.y < 2;
    if(!atSurface){
      localState.energy = clamp(localState.energy - dt*2, 0, 100);
    } else {
      localState.energy = clamp(localState.energy + dt*8, 0, 100);
    }
    localState.depthTile = Math.floor(this.y);
  }
};

/* ============ Camera ============ */
const camera = {
  x: 0, y: 0, targetX:0, targetY:0, zoom:1, targetZoom:1,
  // smooth camera follow
  update(dt){
    // target is player pixel pos
    this.targetX = Player.px - innerWidth/2 + TILE_SIZE/2;
    this.targetY = Player.py - innerHeight/2 + TILE_SIZE/2;
    // zoom driven by depth (deeper -> slight zoom out)
    const depth = clamp(Player.y / 600, 0, 1);
    this.targetZoom = 1 - depth*0.08;

    // lerp towards target
    const t = clamp(dt * 8, 0, 1);
    this.x = lerp(this.x, this.targetX, t);
    this.y = lerp(this.y, this.targetY, t);
    this.zoom = lerp(this.zoom, this.targetZoom, t);
  }
};

/* ============ Renderer ============ */
const Renderer = {
  lastRender:0,
  tileCacheDirty: true,
  render(){
    const now = performance.now();
    const dt = (now - (this.lastRender||now))/1000;
    this.lastRender = now;

    // background
    this.renderBackground();

    // parallax
    this.renderParallax();

    // tiles
    this.renderTiles();

    // entities (player + particles)
    this.renderEntities(dt);

    // lighting overlay
    this.renderLighting();

    // update UI throttled
    updateUI();

    requestAnimationFrame(()=>this.render());
  },

  renderBackground(){
    const c = ctx.bg;
    c.clearRect(0,0,canvases.bg.width,canvases.bg.height);
    // a simple gradient sky
    const g = c.createLinearGradient(0,0,0,canvases.bg.height);
    g.addColorStop(0, '#6ec6ff');
    g.addColorStop(1, '#06202a');
    c.fillStyle = g;
    c.fillRect(0,0,canvases.bg.width,canvases.bg.height);
  },

  renderParallax(){
    const c = ctx.px;
    c.clearRect(0,0,canvases.px.width,canvases.px.height);
    const scrollX = camera.x * 0.02;
    const scrollY = camera.y * 0.02;
    // simple repeating mountain pattern
    c.fillStyle = '#0b2b35';
    c.fillRect(0,canvases.px.height*0.6 + (scrollY%50),canvases.px.width,canvases.px.height*0.4);
    c.globalAlpha = 0.6;
    for(let i=-2;i<6;i++){
      const x = (i*200 + (scrollX%200));
      c.fillStyle = '#123a44';
      c.beginPath();
      c.moveTo(x, canvases.px.height*0.6);
      c.lineTo(x+120, canvases.px.height*0.35);
      c.lineTo(x+240, canvases.px.height*0.6);
      c.closePath();
      c.fill();
    }
    c.globalAlpha = 1;
  },

  renderTiles(){
    const c = ctx.tiles;
    c.clearRect(0,0,canvases.tiles.width,canvases.tiles.height);
    c.save();
    c.translate(-camera.x, -camera.y);
    c.scale(camera.zoom, camera.zoom);
    const startTileX = Math.floor(camera.x / TILE_SIZE) - 2;
    const startTileY = Math.floor(camera.y / TILE_SIZE) - 2;
    const endX = startTileX + Math.ceil(canvasTilesX()) + 4;
    const endY = startTileY + Math.ceil(canvasTilesY()) + 4;
    // only render tiles in view
    for(let ty = startTileY; ty <= endY; ty++){
      for(let tx = startTileX; tx <= endX; tx++){
        const tile = World.getTile(tx, ty);
        if(!tile || tile.type === 'air') continue;
        const tt = TILE_TYPES.find(t=>t.id===tile.type) || TILE_TYPES[0];
        const px = tx * TILE_SIZE;
        const py = ty * TILE_SIZE;
        // darken with depth
        const depthShade = clamp(ty/600,0,1)*0.6;
        c.fillStyle = shadeColor(tt.color, -depthShade*60);
        c.fillRect(px,py, TILE_SIZE, TILE_SIZE);
        // draw a subtle border pixel
        c.strokeStyle = 'rgba(0,0,0,0.12)';
        c.strokeRect(px,py, TILE_SIZE, TILE_SIZE);
      }
    }
    c.restore();
  },

  renderEntities(dt){
    const c = ctx.ent;
    c.clearRect(0,0,canvases.ent.width,canvases.ent.height);
    c.save();
    c.translate(-camera.x, -camera.y);
    c.scale(camera.zoom, camera.zoom);

    // Player - simple pixel sprite
    const px = Player.px, py = Player.py;
    c.fillStyle = '#ffd166';
    c.fillRect(px, py - Player.height + TILE_SIZE/2, TILE_SIZE, Player.height);

    // mining progress ring (if any)
    if(Player.mining.target){
      const t = Player.mining.target;
      const worldPx = t.x * TILE_SIZE + TILE_SIZE/2;
      const worldPy = t.y * TILE_SIZE + TILE_SIZE/2;
      const progress = clamp(Player.mining.progress / Math.max(1, World.getTile(t.x,t.y).hp),0,1);
      c.beginPath();
      c.arc(worldPx, worldPy, TILE_SIZE*0.9, -Math.PI/2, -Math.PI/2 + progress*2*Math.PI);
      c.lineWidth = 3;
      c.strokeStyle = '#fff';
      c.stroke();
    }

    // particles
    ParticleSystem.draw(c, dt);

    c.restore();
  },

  renderLighting(){
    const c = ctx.light;
    c.clearRect(0,0,canvases.light.width,canvases.light.height);
    // darkness overlay
    c.fillStyle = `rgba(2,6,10,${0.35 + clamp(Player.y/1200,0,0.6)})`;
    c.fillRect(0,0,canvases.light.width,canvases.light.height);
    // radial light around player
    const pScreenX = Player.px - camera.x;
    const pScreenY = Player.py - camera.y;
    const radius = localState.lightRadius + localState.pickaxeLevel * 10;
    const grad = c.createRadialGradient(pScreenX,pScreenY, radius*0.1, pScreenX,pScreenY,radius);
    grad.addColorStop(0, 'rgba(255,255,255,0.001)');
    grad.addColorStop(0.4, 'rgba(0,0,0,0.08)');
    grad.addColorStop(1, 'rgba(0,0,0,0.98)');
    c.globalCompositeOperation = 'destination-out';
    c.fillStyle = grad;
    c.beginPath();
    c.arc(pScreenX,pScreenY,radius,0,2*Math.PI);
    c.fill();
    c.globalCompositeOperation = 'source-over';
  }
};

function canvasTilesX(){ return canvases.tiles.width / (TILE_SIZE * camera.zoom); }
function canvasTilesY(){ return canvases.tiles.height / (TILE_SIZE * camera.zoom); }

/* ============ Particle system (pooled) ============ */
const ParticleSystem = {
  pool: [],
  active: [],
  max: 120,
  spawn(x,y, n=10){
    for(let i=0;i<n;i++){
      let p = this.pool.pop() || {x:0,y:0,vx:0,vy:0,life:0,max:0,color:'#fff',size:2};
      p.x = x; p.y = y;
      const ang = Math.random()*Math.PI*2;
      const sp = Math.random()*1.8 + 0.2;
      p.vx = Math.cos(ang)*sp;
      p.vy = Math.sin(ang)*sp;
      p.life = 0; p.max = 0.5 + Math.random()*0.8;
      p.color = ['#fff','#ffd166','#ff8fab'][Math.floor(Math.random()*3)];
      p.size = Math.random()*2 + 1;
      this.active.push(p);
      if(this.active.length > this.max) this.pool.push(this.active.shift());
    }
  },
  draw(ctx, dt){
    for(let i=this.active.length-1;i>=0;i--){
      const p = this.active[i];
      p.life += dt;
      if(p.life >= p.max){
        this.pool.push(...this.active.splice(i,1));
        continue;
      }
      const alpha = 1 - p.life/p.max;
      ctx.globalAlpha = alpha;
      ctx.fillStyle = p.color;
      ctx.fillRect(p.x + p.vx * (p.life*60), p.y + p.vy * (p.life*60), p.size, p.size);
      ctx.globalAlpha = 1;
    }
  }
};

function spawnParticles(px,py, n=12){
  // world coords
  ParticleSystem.spawn(px,py,n);
}

/* ============ Mining logic ============ */

/**
 * mineBlock(x,y)
 * - Subtracts HP, spawns particles, adds ore to inventory when broken.
 */
function mineBlock(x,y){
  const tile = World.getTile(x,y);
  if(!tile || tile.type === 'air' || tile.type === 'bedrock') return;
  tile.hp--;
  if(tile.hp > 0){
    // still not broken
    World.setTile(x,y, tile);
    audio.play('hit');
    spawnParticles(x*TILE_SIZE + TILE_SIZE/2, y*TILE_SIZE + TILE_SIZE/2, 6);
    return;
  }
  // tile broken
  audio.play('break');
  const tileDef = TILE_TYPES.find(t=>t.id===tile.type) || TILE_TYPES[0];
  // check inventory capacity
  const curCount = Object.values(localState.inventory).reduce((a,b)=>a+b,0);
  if(curCount >= localState.backpackSize){
    showFloatingText('Backpack full', (x*TILE_SIZE - camera.x) + 20, (y*TILE_SIZE - camera.y) - 10, '#ff4d4d');
    return; // cannot collect, block remains? We'll turn to dirt to allow progression
  }
  localState.inventory[tile.type] = (localState.inventory[tile.type]||0) + 1;

  // replace tile with dirt after mining (simpler)
  World.setTile(x,y, {type:'dirt', hp:TILE_TYPES.find(t=>t.id==='dirt').hp});
  spawnParticles(x*TILE_SIZE + TILE_SIZE/2, y*TILE_SIZE + TILE_SIZE/2, 18);
  showFloatingText(`+${tileDef.value} ${tileDef.id}`, (x*TILE_SIZE - camera.x)+20, (y*TILE_SIZE - camera.y)-10, '#ffd166');
  updateUI(true);
}

/* ============ Sell / Shop logic ============ */

/**
 * sellAll()
 * - sells entire inventory when at surface (y <= 1).
 */
function sellAll(){
  if(Player.y > 1){
    showFloatingText('Return to surface to sell', innerWidth/2 - 60, 60, '#ffb');
    return;
  }
  const inv = localState.inventory;
  let total = 0;
  for(const id in inv){
    const count = inv[id];
    if(!count) continue;
    const val = TILE_TYPES.find(t=>t.id===id).value;
    total += val * count;
  }
  if(total === 0){
    showFloatingText('Nothing to sell', innerWidth/2 - 40, 60, '#fff');
    audio.play('click');
    return;
  }
  // animate coins: aggregate
  audio.play('sell');
  const prevMoney = localState.money;
  localState.money += total;
  // empty inventory
  for(const id in inv) inv[id]=0;
  // floating big +$ text
  showFloatingText(`+$${total}`, innerWidth/2, 80, '#8ef');
  updateUI(true);
  saveGame();
}

/* Shop definitions */
const shopData = [
  {id:'pick_1', title:'Pickaxe +1', cost:100, effect(){ localState.pickaxeLevel += 1 }},
  {id:'backpack_1', title:'Backpack +10', cost:80, effect(){ localState.backpackSize += 10 }},
  {id:'light_1', title:'Light +40', cost:120, effect(){ localState.lightRadius += 40 }},
  {id:'energy_1', title:'Energy Pack', cost:60, effect(){ localState.energy = Math.min(100, localState.energy + 50) }},
];

function openShop(){
  UI.shop.setAttribute('aria-hidden','false');
  UI.shop.style.display = 'block';
  audio.play('click');
  renderShopItems();
}
function closeShop(){
  UI.shop.setAttribute('aria-hidden','true');
  UI.shop.style.display = 'none';
  audio.play('click');
}

function renderShopItems(){
  UI.shopItems.innerHTML = '';
  for(const item of shopData){
    const btn = document.createElement('button');
    btn.innerText = `Buy $${item.cost}`;
    btn.disabled = (localState.money < item.cost);
    btn.setAttribute('data-id', item.id);
    btn.addEventListener('click', ()=> buyUpgrade(item.id));
    const div = document.createElement('div');
    div.className = 'shop-item';
    div.innerHTML = `<div><strong>${item.title}</strong><div class="meta">${item.cost} coins</div></div>`;
    div.appendChild(btn);
    UI.shopItems.appendChild(div);
  }
}

/**
 * buyUpgrade(upgradeId)
 * - deduct money, apply effect, disable item if purchased/unaffordable.
 */
function buyUpgrade(upgradeId){
  const item = shopData.find(s=>s.id===upgradeId);
  if(!item) return;
  if(localState.money < item.cost) return;
  localState.money -= item.cost;
  // apply
  item.effect();
  localState.upgrades[upgradeId] = true;
  audio.play('buy');
  showFloatingText(`Bought ${item.title}`, innerWidth/2, 80, '#bfffbe');
  renderShopItems();
  updateUI(true);
  saveGame();
}

/* ============ Save / Load ============ */

/**
 * saveGame()
 * - store localState and player progress to localStorage
 */
function saveGame(){
  const state = {
    localState,
    player: {x:Player.x, y:Player.y, pickaxeLevel: localState.pickaxeLevel}
  };
  try {
    localStorage.setItem(SAVE_KEY, JSON.stringify(state));
    // small visual
  } catch(e){
    console.warn('Save failed', e);
  }
}

/**
 * loadGame()
 * - read localStorage and apply state
 */
function loadGame(){
  try {
    const raw = localStorage.getItem(SAVE_KEY);
    if(!raw) return false;
    const parsed = JSON.parse(raw);
    if(parsed.localState) Object.assign(localState, parsed.localState);
    if(parsed.player){
      Player.x = parsed.player.x || Player.x;
      Player.y = parsed.player.y || Player.y;
    }
    // re-init world with seed
    World.init(localState.seed);
    return true;
  } catch(e){
    console.warn('load error', e); return false;
  }
}

/* ============ UI helpers ============ */
function updateUI(force=false){
  // money
  if(force || uiCache.money !== localState.money){
    UI.money.textContent = `Money: $${localState.money}`;
    uiCache.money = localState.money;
  }
  // depth
  if(force || uiCache.depth !== localState.depthTile){
    UI.depth.textContent = `Depth: ${localState.depthTile}`;
    uiCache.depth = localState.depthTile;
  }
  // energy
  if(force || uiCache.energy !== Math.floor(localState.energy)){
    UI.energy.textContent = `Energy: ${Math.floor(localState.energy)}%`;
    uiCache.energy = Math.floor(localState.energy);
  }
  // inventory (throttle)
  const invJSON = JSON.stringify(localState.inventory);
  if(force || uiCache.invJSON !== invJSON){
    UI.inventoryList.innerHTML = '';
    for(const t of TILE_TYPES){
      const li = document.createElement('li');
      li.innerHTML = `<span>${t.id}</span><span>${localState.inventory[t.id]||0}</span>`;
      UI.inventoryList.appendChild(li);
    }
    UI.backpackInfo.textContent = `Capacity: ${localState.backpackSize}`;
    uiCache.invJSON = invJSON;
  }
  // mute button
  UI.muteBtn.textContent = localState.mute ? 'Unmute' : 'Mute';
  audio.enabled = !localState.mute;
}

/* Floating text feedback */
function showFloatingText(text, x, y, color='#fff'){
  const el = document.createElement('div');
  el.className = 'fx-text';
  el.style.left = `${x}px`;
  el.style.top = `${y}px`;
  el.style.color = color;
  el.textContent = text;
  UI.fxLayer.appendChild(el);
  // animate
  el.animate([
    {transform: 'translateY(0) scale(1)', opacity:1},
    {transform: 'translateY(-40px) scale(1.05)', opacity:0}
  ], {duration: 900, easing:'cubic-bezier(.2,.8,.2,1)'});
  setTimeout(()=>el.remove(), 900);
}

/* Utility: shade color */
function shadeColor(hex, percent){
  // hex like #rrggbb
  const num = parseInt(hex.slice(1),16);
  let r = (num>>16) + percent;
  let g = (num>>8 & 0x00FF) + percent;
  let b = (num & 0x0000FF) + percent;
  r = clamp(Math.round(r),0,255);
  g = clamp(Math.round(g),0,255);
  b = clamp(Math.round(b),0,255);
  return `rgb(${r},${g},${b})`;
}

/* ============ Input handling & mobile controls ============ */
const Input = {left:false,right:false,down:false,mine:false};
window.addEventListener('keydown', (e)=>{
  if(e.key === 'ArrowLeft' || e.key === 'a') Input.left = true;
  if(e.key === 'ArrowRight' || e.key === 'd') Input.right = true;
  if(e.key === 'ArrowDown' || e.key === 's') Input.down = true;
  if(e.code === 'Space') Input.mine = true;
});
window.addEventListener('keyup', (e)=>{
  if(e.key === 'ArrowLeft' || e.key === 'a') Input.left = false;
  if(e.key === 'ArrowRight' || e.key === 'd') Input.right = false;
  if(e.key === 'ArrowDown' || e.key === 's') Input.down = false;
  if(e.code === 'Space') Input.mine = false;
});

// mouse/touch: select adjacent tile to player
canvases.tiles.addEventListener('pointerdown', (ev)=>{
  const rect = canvases.tiles.getBoundingClientRect();
  const sx = (ev.clientX - rect.left) + camera.x;
  const sy = (ev.clientY - rect.top) + camera.y;
  const tx = Math.floor(sx / TILE_SIZE);
  const ty = Math.floor(sy / TILE_SIZE);
  // allow mining only adjacent tiles (4-neighbor)
  const px = Math.floor(Player.x);
  const py = Math.floor(Player.y);
  const dx = Math.abs(tx - px), dy = Math.abs(ty - py);
  if(dx + dy <= 1){
    Player.mining.target = {x: tx, y: ty};
    Input.mine = true;
  }
});

canvases.tiles.addEventListener('pointerup', ()=>{ Input.mine = false; Player.mining.target = null; });

/* Mobile UI buttons */
UI.leftBtn?.addEventListener('pointerdown', ()=>Input.left = true);
UI.leftBtn?.addEventListener('pointerup', ()=>Input.left = false);
UI.rightBtn?.addEventListener('pointerdown', ()=>Input.right = true);
UI.rightBtn?.addEventListener('pointerup', ()=>Input.right = false);
UI.downBtn?.addEventListener('pointerdown', ()=>Input.down = true);
UI.downBtn?.addEventListener('pointerup', ()=>Input.down = false);
UI.mineBtn?.addEventListener('pointerdown', ()=>Input.mine = true);
UI.mineBtn?.addEventListener('pointerup', ()=>Input.mine = false);

UI.sellBtn?.addEventListener('click', sellAll);
UI.shopBtn?.addEventListener('click', openShop);
UI.closeShop?.addEventListener('click', closeShop);
UI.continueBtn?.addEventListener('click', ()=>{ finishLoadingAndStart(); });
UI.muteBtn?.addEventListener('click', ()=>{ audio.toggle(); saveGame(); });
UI.motionToggle?.addEventListener('change', (e)=> document.body.style.transition = e.target.checked? '' : 'none');

/* ============ Particles spawn helper wrapper ============ */
function spawnMoneyParticles(x,y){
  for(let i=0;i<6;i++) spawnParticles(x,y,4);
}

/* ============ Init & main loop ============ */

/**
 * initGame()
 * - load assets (placeholder), setup world, load save, setup UI, then start game.
 */
async function initGame(){
  resizeCanvases();
  loadAudioPlaceholders();
  // show loading screen for a beat
  UI.loading.style.display = 'flex';
  UI.continueBtn.hidden = true;

  // initial seed and world
  World.init(localState.seed);
  // minimal "asset" loading delay simulation (assets are inline placeholders)
  await new Promise(r => setTimeout(r, 700));
  UI.loading.querySelector('#loading-text').textContent = 'Ready!';
  UI.continueBtn.hidden = false;
  // attach continue to start or auto-start
  // allow user to click continue; if they don't, auto-start after 1s
  setTimeout(()=>{ if(UI.continueBtn.hidden === false){ finishLoadingAndStart(); } }, 1200);
}

/* Called when loading screen is dismissed */
function finishLoadingAndStart(){
  UI.loading.hidden = true;
  UI.root.hidden = false;

  // load save if present
  loadGame();
  // ensure world uses saved seed
  World.init(localState.seed);

  // show mobile controls if touch
  if(('ontouchstart' in window) || navigator.maxTouchPoints > 0){
    UI.mobileControls.style.display = 'flex';
  }

  // position player (surface)
  Player.x = 32; Player.y = 0;
  camera.x = Player.px - innerWidth/2; camera.y = Player.py - innerHeight/2;

  // shop initial render
  renderShopItems();

  // Start main loop render
  Renderer.render();
  // Game update loop (physics & logic): separate from rendering
  let last = performance.now();
  function tick(){
    const now = performance.now();
    const dt = (now - last) / 1000;
    last = now;

    Player.update(dt, Input);
    camera.update(dt);

    // throttle small UI saves
    if(Math.random() < 0.02) saveGame();

    requestAnimationFrame(tick);
  }
  tick();
}

/* ============ Helper: clickable tile detection for mining (adjacency) ============ */
function canMineTile(tx,ty){
  const px = Math.floor(Player.x), py = Math.floor(Player.y);
  return (Math.abs(px - tx) + Math.abs(py - ty)) <= 1;
}

/* Expose select tile via pointer (already wired) */

/////////////////////// Minimal automated tests for save/load (console) ///////////////////////
function runSaveLoadTest(){
  const before = {money: localState.money, inv: {...localState.inventory}, seed: localState.seed};
  localState.money += 1;
  saveGame();
  loadGame();
  console.assert(localState.seed === before.seed, 'seed preserved');
  console.assert(localState.money !== undefined, 'money exists');
  // revert
  localState.money = before.money;
  saveGame();
}

// helpful debug: place some ores near surface
function seedingForDemo(){
  for(let y=2;y<20;y++){
    for(let x=28;x<36;x++){
      const t = (y%7===0)?'gold': (y%5===0)?'iron': (y%3===0)?'coal':'dirt';
      World.setTile(x,y,{type:t,hp:TILE_TYPES.find(tt=>tt.id===t).hp});
    }
  }
}

/* ============ Utilities: showSimple floating toast ============ */
function showToast(msg){
  showFloatingText(msg, innerWidth/2, 40, '#fff');
}

/* ============ Start ============ */
initGame();

/* Expose key functions to window for debugging and for buttons to call explicitly */
window.initGame = initGame;
window.generateWorld = (seed)=>{ localState.seed = seed; World.init(seed); showToast('World regenerated'); saveGame(); };
window.camera = camera;
window.mineBlock = mineBlock;
window.sellAll = sellAll;
window.openShop = openShop;
window.closeShop = closeShop;
window.buyUpgrade = buyUpgrade;
window.saveGame = saveGame;
window.loadGame = loadGame;
window.updateUI = updateUI;

/* small helper to spawn floating text when needed by outside calls */
window.showFloatingText = showFloatingText;

/* Put a few ores near player for demo playability */
seedingForDemo();

