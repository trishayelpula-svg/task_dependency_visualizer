// Task Dependency Visualizer
// Graph = adjacency list { task: [tasks that depend on it] }
// Sections: parse -> DFS / Kahn algorithms -> structure analysis (components, SCC)
//           -> critical path (CPM) -> layout -> build frames -> render -> controls
const $=id=>document.getElementById(id);
const EX={v:"Design: 3\nBackend: 5\nFrontend: 4\nAPI Tests: 2\nUI Tests: 2\nDocs: 2\nRelease: 1\nDesign -> Backend\nDesign -> Frontend\nBackend -> API Tests\nFrontend -> UI Tests\nAPI Tests -> Release\nUI Tests -> Release\nDocs -> Release",
c:"Design -> Backend\nBackend -> API\nAPI -> Auth\nAuth -> Backend\nAPI -> Release\nDocs -> Release\nX -> Y -> X"};
const PS={dfs:["visit(u):","  color[u] = GRAY; push u on stack","  for each v in adj[u]:","    if color[v] == WHITE: visit(v)","    else if color[v] == GRAY: CYCLE!  (back edge)","  color[u] = BLACK; add u to finish list","order = reverse(finish list)"],
kahn:["compute in-degree of every task","queue = tasks with in-degree 0","while queue is not empty:","  u = dequeue; add u to order","  for each v in adj[u]: in-degree[v] -= 1","    if in-degree[v] == 0: enqueue v","if order has fewer tasks than graph: CYCLE!"]};
let G,pos,fr=[],fi=0,timer=null,mode='dfs',sel=null;
function parse(t){const names=[],adj={},dur={},seen=new Set();let m=0;const add=n=>{if(!adj[n]){adj[n]=[];names.push(n);dur[n]=1}};
 t.split('\n').forEach(l=>{l=l.trim();if(!l)return;const d=l.match(/^([^>]+?)\s*:\s*(\d+(\.\d+)?)$/);if(d){add(d[1].trim());dur[d[1].trim()]=+d[2];return}
  const p=l.split('->').map(x=>x.trim()).filter(Boolean);p.forEach(add);for(let i=0;i<p.length-1;i++){const k=p[i]+'>'+p[i+1];if(!seen.has(k)){seen.add(k);adj[p[i]].push(p[i+1]);m++}}});return{names,adj,dur,m}}
function runDFS(g,rec){const col={},ec={},st=[],fin=[],vis=[];let chk=0;const cycles=[],sig=new Set();g.names.forEach(v=>col[v]='white');
 const N=()=>({...col}),E=()=>({...ec}),X=()=>({stack:st.slice(),list:fin.slice()});
 const f=u=>{col[u]='gray';st.push(u);vis.push(u);rec(`Visit ${u}: mark GRAY (in progress), push on stack`,N(),E(),1,X());
  for(const v of g.adj[u]){chk++;const k=u+'>'+v;ec[k]='act';rec(`Look at edge ${u} → ${v}`,N(),E(),2,X());
   if(col[v]==='white'){ec[k]='tree';rec(`${v} is WHITE (unseen) → go deeper`,N(),E(),3,X());f(v)}
   else if(col[v]==='gray'){ec[k]='back';const c=st.slice(st.indexOf(v)),s=c.slice().sort().join('|');if(!sig.has(s)){sig.add(s);cycles.push(c.concat(v))}
    const nn=N();c.forEach(x=>nn[x]='cyc');rec(`${v} is GRAY (still on our path) → ${u} → ${v} is a BACK EDGE → cycle ${c.concat(v).join(' → ')}`,nn,E(),4,X())}
   else{ec[k]='';rec(`${v} is already BLACK (finished) → skip`,N(),E(),3,X())}}
  st.pop();col[u]='black';fin.push(u);rec(`Finish ${u}: mark BLACK, pop it, add to finish list`,N(),E(),5,X())};
 g.names.forEach(v=>{if(col[v]==='white')f(v)});const o=cycles.length?null:fin.slice().reverse();if(o)rec('Reverse the finish list → valid schedule order',N(),E(),6,X());
 return{cycles,order:o,chk,vis}}
function runKahn(g,rec){const ind={},col={},ec={};g.names.forEach(v=>{ind[v]=0;col[v]='white'});g.names.forEach(u=>g.adj[u].forEach(v=>ind[v]++));
 const q=g.names.filter(v=>!ind[v]),o=[];let chk=0;const N=()=>({...col}),E=()=>({...ec}),X=()=>({indeg:{...ind},queue:q.slice(),list:o.slice()});
 rec('Count the in-degree (unmet prerequisites) of every task',N(),E(),0,X());q.forEach(v=>col[v]='queue');rec('Queue every task with in-degree 0: they can start now',N(),E(),1,X());
 while(q.length){const u=q.shift();o.push(u);col[u]='black';rec(`Take ${u} from the queue and schedule it`,N(),E(),3,X());
  for(const v of g.adj[u]){chk++;ec[u+'>'+v]='tree';ind[v]--;const r=ind[v]===0;if(r){q.push(v);col[v]='queue'}rec(`Remove edge ${u} → ${v}: in-degree(${v}) = ${ind[v]}${r?' → ready, enqueue':''}`,N(),E(),r?5:4,X())}}
 if(o.length<g.names.length){const s=g.names.filter(v=>!o.includes(v));s.forEach(v=>col[v]='cyc');rec(`Queue empty but ${s.join(', ')} never reached in-degree 0 → blocked by a cycle`,N(),E(),6,X());return{cycles:[s],order:null,chk,stuck:true,vis:o}}
 return{cycles:[],order:o,chk,vis:o}}
function structure(g){const und={};g.names.forEach(v=>und[v]=[]);g.names.forEach(u=>g.adj[u].forEach(v=>{und[u].push(v);und[v].push(u)}));
 const seen=new Set(),comps=[];g.names.forEach(v=>{if(seen.has(v))return;const c=[],s=[v];seen.add(v);while(s.length){const u=s.pop();c.push(u);und[u].forEach(w=>{if(!seen.has(w)){seen.add(w);s.push(w)}})}comps.push(c)});
 let idx=0;const I={},low={},on=new Set(),st=[],scc=[];
 const sc=u=>{I[u]=low[u]=idx++;st.push(u);on.add(u);for(const v of g.adj[u]){if(I[v]===undefined){sc(v);low[u]=Math.min(low[u],low[v])}else if(on.has(v))low[u]=Math.min(low[u],I[v])}
  if(low[u]===I[u]){const c=[];let w;do{w=st.pop();on.delete(w);c.push(w)}while(w!==u);scc.push(c)}};
 g.names.forEach(v=>{if(I[v]===undefined)sc(v)});
 return{comps,cyc:scc.filter(c=>c.length>1||g.adj[c[0]].includes(c[0]))}}
function cpm(g,order){const pred={},ES={},EF={},LS={},LF={};g.names.forEach(v=>pred[v]=[]);g.names.forEach(u=>g.adj[u].forEach(v=>pred[v].push(u)));
 order.forEach(v=>{ES[v]=Math.max(0,...pred[v].map(u=>EF[u]));EF[v]=ES[v]+g.dur[v]});const total=Math.max(0,...order.map(v=>EF[v]));
 order.slice().reverse().forEach(v=>{LF[v]=g.adj[v].length?Math.min(...g.adj[v].map(w=>LS[w])):total;LS[v]=LF[v]-g.dur[v]});
 const slack={},crit={};order.forEach(v=>{slack[v]=+(LS[v]-ES[v]).toFixed(6);crit[v]=slack[v]===0});
 let path=[];let cur=order.find(v=>crit[v]&&ES[v]===0);while(cur){path.push(cur);cur=g.adj[cur].find(w=>crit[w]&&ES[w]===EF[cur])}
 return{ES,EF,slack,crit,total,path}}
function layout(){const n=G.names.length;pos={};const o=G.r.order;
 if(o){const lv={},pred={};G.names.forEach(v=>pred[v]=[]);G.names.forEach(u=>G.adj[u].forEach(v=>pred[v].push(u)));o.forEach(v=>lv[v]=Math.max(-1,...pred[v].map(u=>lv[u]))+1);
  const mx=Math.max(0,...o.map(v=>lv[v])),by={};o.forEach(v=>(by[lv[v]]=by[lv[v]]||[]).push(v));
  Object.keys(by).forEach(l=>by[l].forEach((v,i)=>pos[v]={x:mx?45+l*(530/mx):310,y:by[l].length===1?170:40+i*(260/(by[l].length-1))}))}
 else G.names.forEach((v,i)=>{const t=2*Math.PI*i/n-Math.PI/2;pos[v]={x:310+Math.min(240,60+n*22)*Math.cos(t),y:170+135*Math.sin(t)}})}
const fmt=ms=>ms<.01?(ms*1000).toFixed(1)+' µs':ms.toFixed(3)+' ms';
function timeIt(fn){const t=performance.now();for(let i=0;i<2000;i++)fn(G,()=>{});return(performance.now()-t)/2000}
function build(){stop();G=parse($('in').value);fr=[];sel=null;const run=mode==='dfs'?runDFS:runKahn;
 fr.push({msg:'Initial graph — press Run or Step',s:Object.fromEntries(G.names.map(v=>[v,'white'])),e:{},l:-1,x:mode==='dfs'?{stack:[],list:[]}:{indeg:null,queue:[],list:[]}});
 const r=run(G,(msg,s,e,l,x)=>fr.push({msg,s,e,l,x}));G.r=r;layout();
 const S=structure(G);G.S=S;G.cp=r.order?cpm(G,r.order):null;
 const last=fr[fr.length-1];fr.push({msg:r.cycles.length?'❌ Cycle found — a complete schedule is impossible':'✔ Valid schedule found',s:last.s,e:last.e,l:-1,x:last.x});
 $('s1').textContent=`${G.names.length} / ${G.m}`;$('s2').textContent=r.chk;$('s4').textContent=fmt(timeIt(run));$('s5').textContent=G.cp?G.cp.total+' days':'n/a (cycle)';
 const R=$('res');if(r.cycles.length){R.className='bad';R.textContent=r.stuck?'No valid schedule. Blocked tasks: '+r.cycles[0].join(', '):`No valid schedule. ${r.cycles.length} cycle(s): `+r.cycles.map(c=>c.join(' → ')).join('  |  ')}else{R.className='ok';R.textContent='Valid schedule found — every task comes after its prerequisites'}
 $('vis').textContent=r.vis.join(' → ')||'–';
 $('pt').textContent=mode==='dfs'?'Pseudocode — DFS topological sort':"Pseudocode — Kahn's algorithm";$('code').innerHTML=PS[mode].map((t,i)=>`<div id="L${i}">${t.replace(/</g,'&lt;')}</div>`).join('');
 $('sch').innerHTML=G.cp?`<table><tr><th>Task</th><th>Days</th><th>Start</th><th>Finish</th><th>Slack</th></tr>${r.order.map(v=>`<tr class="${G.cp.crit[v]?'cr':''}"><td>${v}</td><td>${G.dur[v]}</td><td>${G.cp.ES[v]}</td><td>${G.cp.EF[v]}</td><td>${G.cp.slack[v]}</td></tr>`).join('')}</table><p><b>Critical path:</b> ${G.cp.path.join(' → ')} = <b>${G.cp.total} days</b></p>`:'<p class="bad">No schedule can be computed while a cycle exists. Remove one dependency from the cycle.</p>';
 $('str').innerHTML=`<p>Connected components: ${S.comps.map(c=>`<span class="chip cm">{${c.join(', ')}}</span>`).join('')}</p><p>Cyclic groups (strongly connected): ${S.cyc.length?S.cyc.map(c=>`<span class="chip cy">${c.join(', ')}</span>`).join(''):'<span class="ok">none — graph is a DAG</span>'}</p>`;
 $('dep').textContent='Click any task in the graph.';$('tbl').innerHTML='';fi=0;draw()}
function draw(){const f=fr[fi],end=fi===fr.length-1,cp=end&&G.cp?G.cp:null;
 $('eg').innerHTML=G.names.flatMap(u=>G.adj[u].map(v=>{const a=pos[u],b=pos[v];let d;if(u===v)d=`M${a.x} ${a.y-20}C${a.x-30} ${a.y-60} ${a.x+30} ${a.y-60} ${a.x+4} ${a.y-21}`;
  else{const dx=b.x-a.x,dy=b.y-a.y,L=Math.hypot(dx,dy)||1,ux=dx/L,uy=dy/L;d=`M${a.x+ux*21} ${a.y+uy*21}L${b.x-ux*24} ${b.y-uy*24}`}
  const c=cp&&cp.crit[u]&&cp.crit[v]&&cp.EF[u]===cp.ES[v]?'crit':(f.e[u+'>'+v]||'');return `<path class="e ${c}" d="${d}" marker-end="url(#a)"/>`})).join('');
 $('ng').innerHTML=G.names.map((v,i)=>`<g class="n ${f.s[v]==='white'?'':f.s[v]} ${cp&&cp.crit[v]?'crit':''} ${sel===v?'sel':''}" data-i="${i}"><circle cx="${pos[v].x}" cy="${pos[v].y}" r="20"/><text x="${pos[v].x}" y="${pos[v].y}">${v.length>7?v.slice(0,6)+'…':v}</text></g>`).join('');
 $('msg').textContent=f.msg;$('s3').textContent=`${fi+1}/${fr.length}`;
 document.querySelectorAll('pre div').forEach(d=>d.classList.remove('on'));if(f.l>=0&&$('L'+f.l))$('L'+f.l).classList.add('on');
 const T=(a,c)=>a.length?a.map(x=>`<span class="tok ${c||''}">${x}</span>`).join(''):'<em>empty</em>';
 $('sb').innerHTML=mode==='dfs'?`<p><b>Stack (current path):</b> ${T(f.x.stack)}</p><p><b>Finish list:</b> ${T(f.x.list,'f')}</p>`
 :`<p><b>In-degrees:</b> ${f.x.indeg?G.names.map(v=>`<span class="tok ${f.x.indeg[v]===0?'z':''}">${v}: ${f.x.indeg[v]}</span>`).join(''):'<em>not computed yet</em>'}</p><p><b>Queue:</b> ${T(f.x.queue,'z')}</p><p><b>Order so far:</b> ${T(f.x.list,'f')}</p>`;
 $('ord').innerHTML=end&&G.r.order?G.r.order.map((v,i)=>`<span class="chip">${i+1}. ${v}</span>`).join(''):''}
function reach(s,adj){const seen=new Set(),st=[s];while(st.length){const u=st.pop();for(const v of adj[u]||[])if(!seen.has(v)){seen.add(v);st.push(v)}}return[...seen]}
$('ng').onclick=e=>{const g=e.target.closest('.n');if(!g)return;const v=G.names[+g.dataset.i];sel=v;const rev={};G.names.forEach(x=>rev[x]=[]);G.names.forEach(u=>G.adj[u].forEach(w=>rev[w].push(u)));
 const need=reach(v,rev),blk=reach(v,G.adj),ch=(a,c)=>a.length?a.map(x=>`<span class="chip ${c}">${x}</span>`).join(''):'<em>none</em>';
 $('dep').innerHTML=`<p><b>${v}</b> (${G.dur[v]} day${G.dur[v]==1?'':'s'})</p><p>Depends on (all prerequisites, via DFS): ${ch(need,'pre')}</p><p>Blocks (everything waiting on it): ${ch(blk,'blk')}</p>${need.includes(v)?'<p class="bad">This task is inside a cycle.</p>':''}`;draw()};
$('cmp').onclick=()=>{$('tbl').innerHTML='<tr><th>Algorithm</th><th>Edge checks</th><th>Avg time</th><th>Complexity</th><th>Result</th></tr>'+[['DFS Topological Sort',runDFS],["Kahn's Algorithm",runKahn]].map(([n,fn])=>{const r=fn(G,()=>{});
 const out=r.cycles.length?(fn===runDFS?`${r.cycles.length} cycle(s): `+r.cycles.map(c=>c.join('→')).join(' | '):'Blocked: '+r.cycles[0].join(', ')):r.order.join(' → ');
 return `<tr><td>${n}</td><td>${r.chk}</td><td>${fmt(timeIt(fn))}</td><td>O(V + E)</td><td>${out}</td></tr>`}).join('')};
function tick(){if(fi<fr.length-1){fi++;draw()}else stop()}
function play(){if(timer)return stop();if(fi>=fr.length-1)fi=0;$('play').textContent='⏸ Pause';timer=setInterval(tick,Math.max(40,1010-$('spd').value*10))}
function stop(){clearInterval(timer);timer=null;$('play').textContent='▶ Run'}
function setMode(m){mode=m;$('tD').classList.toggle('on',m==='dfs');$('tK').classList.toggle('on',m==='kahn');build()}
$('tD').onclick=()=>setMode('dfs');$('tK').onclick=()=>setMode('kahn');$('in').oninput=build;
$('bV').onclick=()=>{$('in').value=EX.v;build()};$('bC').onclick=()=>{$('in').value=EX.c;build()};
$('play').onclick=play;$('step').onclick=()=>{stop();tick()};$('back').onclick=()=>{stop();if(fi>0){fi--;draw()}};$('reset').onclick=()=>{stop();fi=0;draw()};$('spd').oninput=()=>{if(timer){stop();play()}};
$('in').value=EX.v;build();