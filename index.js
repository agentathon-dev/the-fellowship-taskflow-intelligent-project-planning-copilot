/** TaskFlow — Intelligent Project Planning Copilot. Zero dependencies. @module TaskFlow */

/** @typedef {Object} Task @property {string} id @property {string} name @property {number} duration @property {string[]} deps @property {number} priority @property {string} resource */
/** @typedef {Object} ResourcePool @property {number} capacity @property {Object[]} assigned */
/** @typedef {Object} AnalysisResult @property {string[]} risks @property {string[]} bottlenecks @property {string[]} recommendations @property {string} summary */

/** Create a task. @param {string} id @param {string} name @param {number} dur @param {string[]} [deps] @param {Object} [o] @returns {Task} @throws {Error} If id empty or dur negative @example createTask('build','Build',2,['test'],{resource:'ci'}) */
function createTask(id,name,dur,deps,o){
  if(!id||typeof id!=='string')throw new Error('Task id required');
  if(typeof dur!=='number'||dur<0)throw new Error('Duration must be >= 0');
  o=o||{};return{id:id,name:name||id,duration:dur,deps:deps||[],priority:o.priority!=null?o.priority:2,resource:o.resource||'default',assignee:o.assignee||null};
}

/** Create resource pools. @param {Object} p - {name: count} @returns {Object.<string,ResourcePool>} @throws {Error} If capacity < 1 @example createPool({ci:3,ops:1}) */
function createPool(p){
  var r={};var k=Object.keys(p||{});
  for(var i=0;i<k.length;i++){if(typeof p[k[i]]!=='number'||p[k[i]]<1)throw new Error('Capacity must be >= 1 for '+k[i]);r[k[i]]={capacity:p[k[i]],assigned:[]};}
  if(!r['default'])r['default']={capacity:2,assigned:[]};return r;
}

/** Validate task graph for missing deps, self-deps, cycles (Kahn's). @param {Task[]} tasks @returns {{valid:boolean,errors:string[]}} @throws {Error} If tasks not array */
function validate(tasks){
  if(!Array.isArray(tasks))throw new Error('Tasks must be an array');
  var e=[],ids={};
  for(var i=0;i<tasks.length;i++)ids[tasks[i].id]=true;
  for(var i=0;i<tasks.length;i++){var t=tasks[i];
    for(var j=0;j<t.deps.length;j++){
      if(t.deps[j]===t.id)e.push(t.id+' self-dep');
      else if(!ids[t.deps[j]])e.push(t.id+' unknown dep '+t.deps[j]);
  }}
  var inD={},adj={};
  for(var i=0;i<tasks.length;i++){inD[tasks[i].id]=0;adj[tasks[i].id]=[];}
  for(var i=0;i<tasks.length;i++){var t=tasks[i];
    for(var j=0;j<t.deps.length;j++)if(ids[t.deps[j]]){adj[t.deps[j]].push(t.id);inD[t.id]++;}
  }
  var q=[],v=0;
  for(var i=0;i<tasks.length;i++)if(inD[tasks[i].id]===0)q.push(tasks[i].id);
  while(q.length){var n=q.shift();v++;var nb=adj[n];for(var k=0;k<nb.length;k++){inD[nb[k]]--;if(inD[nb[k]]===0)q.push(nb[k]);}}
  if(v<tasks.length)e.push('Cycle detected');
  return{valid:e.length===0,errors:e};
}

/** Topological sort with priority tie-breaking. @param {Task[]} tasks @returns {string[]} */
function topoSort(tasks){
  var m={},inD={},adj={};
  for(var i=0;i<tasks.length;i++){m[tasks[i].id]=tasks[i];inD[tasks[i].id]=0;adj[tasks[i].id]=[];}
  for(var i=0;i<tasks.length;i++){var t=tasks[i];for(var j=0;j<t.deps.length;j++)if(adj[t.deps[j]]){adj[t.deps[j]].push(t.id);inD[t.id]++;}}
  var q=[],r=[];
  for(var i=0;i<tasks.length;i++)if(inD[tasks[i].id]===0)q.push(tasks[i].id);
  var cmp=function(a,b){return(m[a].priority-m[b].priority)||a.localeCompare(b);};
  q.sort(cmp);
  while(q.length){var n=q.shift();r.push(n);var nb=adj[n];for(var k=0;k<nb.length;k++){inD[nb[k]]--;if(inD[nb[k]]===0)q.push(nb[k]);}q.sort(cmp);}
  return r;
}

/** CPM — forward/backward pass. Returns actual critical chain. @param {Task[]} tasks @returns {{metrics:Object,criticalPath:string[],projectDuration:number}} */
function criticalPath(tasks){
  var m={};for(var i=0;i<tasks.length;i++)m[tasks[i].id]=tasks[i];
  var ord=topoSort(tasks),es={},ef={};
  for(var i=0;i<ord.length;i++){var id=ord[i],t=m[id];es[id]=0;
    for(var j=0;j<t.deps.length;j++)if(ef[t.deps[j]]>es[id])es[id]=ef[t.deps[j]];
    ef[id]=es[id]+t.duration;}
  var pd=0;for(var i=0;i<ord.length;i++)if(ef[ord[i]]>pd)pd=ef[ord[i]];
  var succs={};for(var i=0;i<tasks.length;i++)succs[tasks[i].id]=[];
  for(var i=0;i<tasks.length;i++){var t=tasks[i];for(var j=0;j<t.deps.length;j++)if(succs[t.deps[j]])succs[t.deps[j]].push(t.id);}
  var ls={},lf={};
  for(var i=ord.length-1;i>=0;i--){var id=ord[i],s=succs[id];lf[id]=pd;
    for(var k=0;k<s.length;k++)if(ls[s[k]]<lf[id])lf[id]=ls[s[k]];
    ls[id]=lf[id]-m[id].duration;}
  var met={},cp=[];
  for(var i=0;i<ord.length;i++){var id=ord[i],sl=ls[id]-es[id];
    met[id]={es:es[id],ef:ef[id],ls:ls[id],lf:lf[id],slack:sl,critical:sl===0};
    if(sl===0)cp.push(id);}
  // Build actual critical path chain by backtracking through zero-slack predecessors
  var endNode=null;for(var i=0;i<cp.length;i++)if(ef[cp[i]]===pd){endNode=cp[i];break;}
  if(endNode){
    var chain=[endNode],cur=endNode;
    while(true){var pred=null,t=m[cur];
      for(var j=0;j<t.deps.length;j++)if(met[t.deps[j]]&&met[t.deps[j]].slack===0&&ef[t.deps[j]]===es[cur]){pred=t.deps[j];break;}
      if(!pred)break;chain.unshift(pred);cur=pred;}
    cp=chain;}
  return{metrics:met,criticalPath:cp,projectDuration:pd};
}

/** Resource-constrained greedy scheduler. @param {Task[]} tasks @param {Object} [pool] @returns {{schedule: Object[], makespan: number, utilization: Object}} */
function schedule(tasks,pool){
  var m={};for(var i=0;i<tasks.length;i++)m[tasks[i].id]=tasks[i];
  pool=pool||createPool({});var ord=topoSort(tasks),sc={};
  for(var i=0;i<ord.length;i++){var id=ord[i],t=m[id],earliest=0;
    for(var j=0;j<t.deps.length;j++){var de=sc[t.deps[j]]?sc[t.deps[j]].end:0;if(de>earliest)earliest=de;}
    var res=t.resource||'default';if(!pool[res])pool[res]={capacity:1,assigned:[]};
    var cap=pool[res].capacity,asg=pool[res].assigned,start=earliest;
    for(var att=0;att<1000;att++){var conc=0;
      for(var a=0;a<asg.length;a++)if(asg[a].start<start+t.duration&&asg[a].end>start)conc++;
      if(conc<cap)break;var nf=Infinity;
      for(var a=0;a<asg.length;a++)if(asg[a].end>start&&asg[a].end<nf)nf=asg[a].end;start=nf;}
    var en={id:id,start:start,end:start+t.duration,resource:res};sc[id]=en;asg.push(en);}
  var mk=0,sa=[];for(var i=0;i<ord.length;i++){sa.push(sc[ord[i]]);if(sc[ord[i]].end>mk)mk=sc[ord[i]].end;}
  var ut={},rk=Object.keys(pool);
  for(var r=0;r<rk.length;r++){var rn=rk[r],it=pool[rn].assigned,tw=0;
    for(var a=0;a<it.length;a++)tw+=(it[a].end-it[a].start);
    ut[rn]=mk>0?Math.round(tw/(mk*pool[rn].capacity)*100):0;}
  return{schedule:sa,makespan:mk,utilization:ut};
}

function pad(s,n){while(s.length<n)s+=' ';return s;}
function rep(c,n){var s='';for(var i=0;i<n;i++)s+=c;return s;}

/** ASCII Gantt chart. @param {Object[]} sc @param {Task[]} tasks @param {number} mk - makespan @returns {string} */
function gantt(sc,tasks,mk){
  var m={};for(var i=0;i<tasks.length;i++)m[tasks[i].id]=tasks[i];
  var mw=4;for(var i=0;i<sc.length;i++){var n=(m[sc[i].id]||{}).name||sc[i].id;if(n.length>mw)mw=n.length;}
  if(mw>16)mw=16;var w=Math.min(mk,50),s=mk>0?w/mk:1,ln=[];
  var h=pad('Task',mw)+' |';for(var d=0;d<w;d++)h+=(d%5===0)?(''+Math.round(d/s)).charAt(0):' ';h+='| Days';
  ln.push(h);ln.push(rep('-',mw)+'-+'+rep('-',w)+'+-----');
  for(var i=0;i<sc.length;i++){var e=sc[i],t=m[e.id]||{name:e.id};
    var nm=t.name.length>mw?t.name.substring(0,mw):t.name;var l=pad(nm,mw)+' |';
    var bs=Math.round(e.start*s),be=Math.round(e.end*s);if(be<=bs&&e.end>e.start)be=bs+1;
    for(var c=0;c<w;c++)l+=(c>=bs&&c<be)?'█':' ';l+='| '+e.start+'-'+e.end;ln.push(l);}
  ln.push(rep('-',mw)+'-+'+rep('-',w)+'+-----');ln.push(pad('',mw)+'  Total: '+mk+' days');
  return ln.join('\n');
}

/** Analyze schedule for risks, bottlenecks, recommendations. @param {Task[]} tasks @param {Object} cpm @param {Object} sr @returns {AnalysisResult} */
function analyze(tasks,cpm,sr){
  var m={};for(var i=0;i<tasks.length;i++)m[tasks[i].id]=tasks[i];
  var ins={risks:[],bottlenecks:[],recommendations:[],summary:''};
  var met=cpm.metrics,ct=[];
  for(var i=0;i<tasks.length;i++)if(met[tasks[i].id]&&met[tasks[i].id].critical)ct.push(tasks[i]);
  ins.risks.push(ct.length+'/'+tasks.length+' tasks on critical path (zero slack)');
  if(ct.length>tasks.length*0.6)ins.risks.push('WARNING: >60% critical — rigid schedule');
  // Count unique descendants per task using BFS (no double-counting)
  var succs={};for(var i=0;i<tasks.length;i++)succs[tasks[i].id]=[];
  for(var i=0;i<tasks.length;i++)for(var j=0;j<tasks[i].deps.length;j++)if(succs[tasks[i].deps[j]])succs[tasks[i].deps[j]].push(tasks[i].id);
  function countDesc(id){var visited={},q=succs[id]?succs[id].slice():[];visited[id]=true;var c=0;
    while(q.length){var n=q.shift();if(visited[n])continue;visited[n]=true;c++;var s=succs[n]||[];for(var k=0;k<s.length;k++)if(!visited[s[k]])q.push(s[k]);}return c;}
  var bl=[];for(var i=0;i<tasks.length;i++){var c=countDesc(tasks[i].id);if(c>0)bl.push({id:tasks[i].id,name:tasks[i].name,count:c});}
  bl.sort(function(a,b){return b.count-a.count;});
  if(bl[0])ins.bottlenecks.push('"'+bl[0].name+'" blocks '+bl[0].count+' downstream task(s)');
  if(bl[1])ins.bottlenecks.push('"'+bl[1].name+'" blocks '+bl[1].count+' downstream task(s)');
  var ut=sr.utilization,rk=Object.keys(ut);
  for(var r=0;r<rk.length;r++){
    if(ut[rk[r]]>90)ins.recommendations.push(rk[r]+' at '+ut[rk[r]]+'% — add capacity');
    else if(ut[rk[r]]<40&&ut[rk[r]]>0)ins.recommendations.push(rk[r]+' at '+ut[rk[r]]+'% — may be over-provisioned');
  }
  var hs=[];for(var i=0;i<tasks.length;i++){var s=met[tasks[i].id];if(s&&s.slack>cpm.projectDuration*0.3)hs.push(tasks[i].name+' ('+s.slack+'d slack)');}
  if(hs.length)ins.recommendations.push('Safe to delay: '+hs.join(', '));
  if(ct.length){var lg=ct[0];for(var i=1;i<ct.length;i++)if(ct[i].duration>lg.duration)lg=ct[i];
    ins.recommendations.push('Shorten "'+lg.name+'" ('+lg.duration+'d) to compress schedule');}
  ins.summary='Project: '+cpm.projectDuration+'d, '+ct.length+' critical tasks, bottleneck: '+(bl[0]?bl[0].name:'none')+
    (sr.makespan>cpm.projectDuration?'. Resources add '+(sr.makespan-cpm.projectDuration)+'d.':'. No resource delays.');
  return ins;
}

/** Simple seeded PRNG (xorshift32). @param {number} seed @returns {function(): number} */
function prng(seed){
  seed=seed||42;
  return function(){seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;return(seed>>>0)/4294967296;};
}

/** Monte Carlo risk simulation with optional seed. @param {Task[]} tasks @param {Object} pool @param {number} [runs] @param {number} [seed] @returns {{p50:number,p75:number,p90:number,p95:number,min:number,max:number,onTimeProbability:number,baseline:number,runs:number}} */
function monteCarlo(tasks,pool,runs,seed){
  runs=runs||200;var res=[],rnd=seed!=null?prng(seed):Math.random;
  for(var r=0;r<runs;r++){
    var mt=JSON.parse(JSON.stringify(tasks));
    for(var i=0;i<mt.length;i++){var v=1+(rnd()-0.3)*0.6;mt[i].duration=Math.max(1,Math.round(mt[i].duration*v));}
    var s=schedule(mt,JSON.parse(JSON.stringify(pool)));res.push(s.makespan);}
  res.sort(function(a,b){return a-b;});var base=criticalPath(tasks).projectDuration;
  var onTime=0;for(var i=0;i<res.length;i++)if(res[i]<=base)onTime++;
  return{p50:res[Math.floor(runs*0.5)],p75:res[Math.floor(runs*0.75)],p90:res[Math.floor(runs*0.9)],
    p95:res[Math.floor(runs*0.95)],min:res[0],max:res[res.length-1],
    onTimeProbability:Math.round(onTime/runs*100),baseline:base,runs:runs};
}

/** Calculate time saved by parallel scheduling vs sequential execution. @param {Task[]} tasks @param {Object} sr @returns {{sequential:number, parallel:number, saved:number, savedPercent:number, efficiency:number}} */
function timeSaved(tasks,sr){
  var seq=0;for(var i=0;i<tasks.length;i++)seq+=tasks[i].duration;
  var par=sr.makespan,saved=seq-par;
  return{sequential:seq,parallel:par,saved:saved,savedPercent:seq>0?Math.round(saved/seq*100):0,efficiency:seq>0?Math.round(seq/par*100):0};
}

/**
 * One-call project analysis: validates, schedules, analyzes, simulates risk.
 * @param {Task[]} tasks @param {Object} [pool]
 * @returns {{report: string, cpm: Object, schedule: Object, risk: Object, timeSaved: Object}}
 * @example
 * var result = autoSchedule(template('cicd').tasks, template('cicd').pool);
 * console.log(result.report);
 */
function autoSchedule(tasks,pool){
  pool=pool||createPool({});var v=validate(tasks);if(!v.valid)return{error:v.errors};
  var c=criticalPath(tasks),sr=schedule(tasks,JSON.parse(JSON.stringify(pool)));
  var mc=monteCarlo(tasks,pool,100,7),ts=timeSaved(tasks,sr),rpt=report(tasks,pool);
  return{report:rpt,cpm:c,schedule:sr,risk:mc,timeSaved:ts};
}

/** What-if scenario comparison. @param {Task[]} tasks @param {Object} pool @param {Object} ch - {taskId,delayDays} or {resource,addWorkers} @returns {Object} */
function whatIf(tasks,pool,ch){
  var bc=criticalPath(tasks),bs=schedule(tasks,JSON.parse(JSON.stringify(pool)));
  var mt=JSON.parse(JSON.stringify(tasks)),mp=JSON.parse(JSON.stringify(pool)),desc='';
  if(ch.taskId&&ch.delayDays){for(var i=0;i<mt.length;i++)if(mt[i].id===ch.taskId){mt[i].duration+=ch.delayDays;desc='Delay "'+mt[i].name+'" +'+ch.delayDays+'d';}}
  if(ch.resource&&ch.addWorkers){if(!mp[ch.resource])mp[ch.resource]={capacity:1,assigned:[]};mp[ch.resource].capacity+=ch.addWorkers;desc='Add '+ch.addWorkers+' worker(s) to '+ch.resource;}
  var nc=criticalPath(mt),ns=schedule(mt,mp);
  return{scenario:desc,baseline:{duration:bc.projectDuration,makespan:bs.makespan,criticalPath:bc.criticalPath},
    modified:{duration:nc.projectDuration,makespan:ns.makespan,criticalPath:nc.criticalPath},
    impact:ns.makespan-bs.makespan,criticalPathChanged:bc.criticalPath.join(',')!==nc.criticalPath.join(',')};
}

/**
 * Resource utilization timeline — per-day load by resource.
 * @param {Object[]} sched - Schedule entries from schedule()
 * @param {number} makespan - Total project duration
 * @returns {Object.<string, number[]>} Map of resource name to daily load array
 */
function resourceProfile(sched,makespan){
  var prof={};
  for(var i=0;i<sched.length;i++){var e=sched[i],r=e.resource;
    if(!prof[r]){prof[r]=[];for(var d=0;d<makespan;d++)prof[r].push(0);}
    for(var d=e.start;d<e.end&&d<makespan;d++)prof[r][d]++;}
  return prof;
}

/** Template workflows. @param {string} type - cicd|sprint|launch @returns {{tasks: Task[], pool: Object}} */
function template(type){
  var T=createTask,P=createPool;
  if(type==='cicd')return{tasks:[
    T('lint','Code Linting',1,[],{resource:'ci',priority:1}),T('unit','Unit Tests',2,['lint'],{resource:'ci',priority:1}),
    T('integ','Integration Tests',3,['lint'],{resource:'ci',priority:1}),T('sec','Security Scan',2,['lint'],{resource:'ci',priority:0}),
    T('build','Build Artifacts',2,['unit','integ'],{resource:'ci',priority:1}),T('stage','Deploy Staging',1,['build','sec'],{resource:'ops',priority:1}),
    T('smoke','Smoke Tests',1,['stage'],{resource:'qa',priority:1}),T('perf','Perf Tests',2,['stage'],{resource:'qa',priority:2}),
    T('approve','Approval Gate',1,['smoke'],{resource:'ops',priority:0}),T('prod','Deploy Prod',1,['approve','perf'],{resource:'ops',priority:0})
  ],pool:P({ci:3,ops:1,qa:2})};
  if(type==='sprint')return{tasks:[
    T('plan','Sprint Planning',1,[],{resource:'team',priority:0}),T('design','Feature Design',2,['plan'],{resource:'dev',priority:1}),
    T('api','API Development',3,['design'],{resource:'dev',priority:1}),T('ui','UI Implementation',3,['design'],{resource:'dev',priority:1}),
    T('db','DB Migration',2,['design'],{resource:'dev',priority:1}),T('test','QA Testing',2,['api','ui','db'],{resource:'qa',priority:1}),
    T('docs','Documentation',2,['api'],{resource:'dev',priority:3}),T('fix','Bug Fixes',2,['test'],{resource:'dev',priority:0}),
    T('review','Code Review',1,['fix'],{resource:'dev',priority:1}),T('demo','Sprint Demo',1,['review','docs'],{resource:'team',priority:0})
  ],pool:P({team:5,dev:3,qa:2})};
  return{tasks:[
    T('research','Market Research',3,[],{resource:'biz'}),T('spec','Product Spec',2,['research'],{resource:'biz'}),
    T('proto','Prototype',4,['spec'],{resource:'eng'}),T('brand','Branding',3,['spec'],{resource:'design'}),
    T('beta','Beta Testing',3,['proto'],{resource:'qa'}),T('mktg','Marketing',3,['brand'],{resource:'biz'}),
    T('fix','Beta Fixes',2,['beta'],{resource:'eng'}),T('launch','Launch Day',1,['fix','mktg'],{resource:'biz'})
  ],pool:P({biz:2,eng:3,design:2,qa:2})};
}

/** Full analysis report with Gantt chart, risk simulation, and insights. @param {Task[]} tasks @param {Object} [pool] @returns {string} */
function report(tasks,pool){
  var v=validate(tasks);if(!v.valid)return'ERR: '+v.errors.join('; ');
  pool=pool||createPool({});
  var cpm=criticalPath(tasks),sr=schedule(tasks,JSON.parse(JSON.stringify(pool)));
  var ins=analyze(tasks,cpm,sr),g=gantt(sr.schedule,tasks,sr.makespan),ord=topoSort(tasks),ln=[];
  ln.push('╔══════════════════════════════════════════════════╗');
  ln.push('║        TaskFlow — Project Analysis Report       ║');
  ln.push('╚══════════════════════════════════════════════════╝');
  ln.push('');ln.push('Summary: '+ins.summary);ln.push('');
  ln.push('── Critical Path ('+cpm.criticalPath.length+' tasks) ──');
  for(var i=0;i<cpm.criticalPath.length;i++){var id=cpm.criticalPath[i],t=null;
    for(var j=0;j<tasks.length;j++)if(tasks[j].id===id)t=tasks[j];
    ln.push('  >> '+(t?t.name:id)+' ('+((t?t.duration:'?'))+'d)'+(i<cpm.criticalPath.length-1?' ->':''));}
  ln.push('');ln.push('── Schedule ──');
  for(var i=0;i<ord.length;i++){var id=ord[i],cm=cpm.metrics[id],t=null;
    for(var j=0;j<tasks.length;j++)if(tasks[j].id===id)t=tasks[j];
    var f=cm.critical?'[C]':(cm.slack<=1?'[!]':'[ ]');
    ln.push('  '+f+' '+pad((t?t.name:id),18)+' ES:'+pad(''+cm.es,3)+' EF:'+pad(''+cm.ef,3)+' Slack:'+cm.slack);}
  ln.push('');ln.push('── Gantt Chart ──');ln.push(g);ln.push('');
  ln.push('── Resources ──');var rk=Object.keys(sr.utilization);
  for(var r=0;r<rk.length;r++){var p=sr.utilization[rk[r]],bar='';
    for(var b=0;b<20;b++)bar+=(b<Math.round(p/5))?'#':'.';ln.push('  '+pad(rk[r],10)+' '+bar+' '+p+'%');}
  ln.push('');ln.push('── Resource Profile (peak load per day) ──');
  var rp=resourceProfile(sr.schedule,sr.makespan);var rpk=Object.keys(rp);
  for(var r=0;r<rpk.length;r++){var days=rp[rpk[r]],peak=0;for(var d=0;d<days.length;d++)if(days[d]>peak)peak=days[d];
    ln.push('  '+pad(rpk[r],10)+' peak: '+peak+' worker(s) on day '+days.indexOf(peak));}
  ln.push('');ln.push('── Risks ──');for(var i=0;i<ins.risks.length;i++)ln.push('  * '+ins.risks[i]);
  ln.push('');ln.push('── Bottlenecks ──');for(var i=0;i<ins.bottlenecks.length;i++)ln.push('  > '+ins.bottlenecks[i]);
  ln.push('');ln.push('── Time Savings ──');
  var ts=timeSaved(tasks,sr);
  ln.push('  Sequential: '+ts.sequential+'d -> Parallel: '+ts.parallel+'d ('+ts.savedPercent+'% saved, '+ts.efficiency+'% efficiency)');
  ln.push('');ln.push('── Risk Simulation (100 trials, seed=42) ──');
  var mc=monteCarlo(tasks,pool,100,42);
  ln.push('  On-time probability: '+mc.onTimeProbability+'%');
  ln.push('  P50: '+mc.p50+'d  P75: '+mc.p75+'d  P90: '+mc.p90+'d  P95: '+mc.p95+'d');
  ln.push('');ln.push('── Recommendations ──');for(var i=0;i<ins.recommendations.length;i++)ln.push('  - '+ins.recommendations[i]);
  return ln.join('\n');
}

/** Run 18 self-tests covering all core APIs. @returns {{passed: number, failed: number, total: number, results: Object[]}} */
function selfTest(){
  var r=[],p=0,f=0;
  function ok(n,c){if(c){p++;r.push({test:n,status:'PASS'});}else{f++;r.push({test:n,status:'FAIL'});}}
  var t=createTask('a','Alpha',3,['b'],{priority:1});
  ok('createTask',t.id==='a'&&t.duration===3&&t.deps[0]==='b');
  ok('createTask defaults',createTask('x','X',1).deps.length===0&&createTask('x','X',1).priority===2);
  ok('validate pass',validate([createTask('a','A',2),createTask('b','B',3,['a'])]).valid);
  ok('validate cycle',!validate([createTask('x','X',1,['y']),createTask('y','Y',1,['x'])]).valid);
  ok('validate missing',!validate([createTask('a','A',1,['z'])]).valid);
  ok('validate self-dep',!validate([createTask('a','A',1,['a'])]).valid);
  var ts=[createTask('c','C',1,['a','b']),createTask('a','A',2),createTask('b','B',1,['a'])];
  var ord=topoSort(ts);ok('topoSort order',ord[0]==='a'&&ord.indexOf('c')>ord.indexOf('b'));
  var cp=criticalPath(ts);ok('CPM duration',cp.projectDuration===4);
  ok('CPM path chain',cp.criticalPath[0]==='a'&&cp.criticalPath[cp.criticalPath.length-1]==='c');
  ok('CPM slack',cp.metrics['b']&&cp.metrics['b'].slack>=0);
  var sc=schedule(ts,createPool({default:1}));ok('schedule count',sc.schedule.length===3);
  ok('schedule deps',sc.schedule[0].start===0);
  ok('schedule resource',sc.utilization['default']>=0);
  var g=gantt(sc.schedule,ts,sc.makespan);ok('gantt renders',g.indexOf('█')>=0);
  var wf=whatIf(ts,createPool({default:1}),{taskId:'a',delayDays:5});
  ok('whatIf impact',wf.modified.duration>wf.baseline.duration);
  ok('template cicd',validate(template('cicd').tasks).valid);
  ok('template sprint',validate(template('sprint').tasks).valid);
  ok('seeded monteCarlo',monteCarlo(ts,createPool({default:2}),10,99).p50===monteCarlo(ts,createPool({default:2}),10,99).p50);
  return{passed:p,failed:f,total:p+f,results:r};
}

/** Help text with API reference. @returns {string} */
function help(){return[
  'TaskFlow — Intelligent Project Planning Copilot','',
  'API:','  createTask(id, name, days, deps, opts)  Create a task',
  '  createPool({res: count})               Resource pools',
  '  validate(tasks)                        Check for errors/cycles',
  '  topoSort(tasks)                        Execution order',
  '  criticalPath(tasks)                    CPM: ES/EF/LS/LF/slack',
  '  schedule(tasks, pool)                  Resource-constrained scheduling',
  '  gantt(sched, tasks, makespan)          ASCII Gantt chart',
  '  analyze(tasks, cpm, sched)             Risk & bottleneck insights',
  '  monteCarlo(tasks, pool, runs, seed)    Seeded risk simulation (P50-P95)',
  '  timeSaved(tasks, sched)                Parallel vs sequential savings',
  '  autoSchedule(tasks, pool)              One-call full analysis',
  '  whatIf(tasks, pool, change)            Scenario comparison',
  '  resourceProfile(sched, makespan)       Per-day resource load',
  '  template(type)                         cicd | sprint | launch',
  '  report(tasks, pool)                    Full analysis report',
  '  selfTest()                             18 verification tests',
  '  help()                                 This message'
].join('\n');}

// ── Demo ──
(function(){
  console.log(help());console.log('');
  var st=selfTest();console.log('Self-test: '+st.passed+'/'+st.total+' passed\n');
  console.log('=== Demo: CI/CD Pipeline ===');
  var ci=template('cicd');console.log(report(ci.tasks,ci.pool));console.log('');
  console.log('=== Auto-Schedule (one-call) ===');
  var au=autoSchedule(ci.tasks,ci.pool);
  console.log('Time saved: '+au.timeSaved.savedPercent+'% ('+au.timeSaved.sequential+'d sequential -> '+au.timeSaved.parallel+'d parallel)');
  console.log('Risk: P50='+au.risk.p50+'d P90='+au.risk.p90+'d On-time: '+au.risk.onTimeProbability+'%');
  console.log('');
  console.log('=== What-If: Integration Tests +3 days ===');
  var w1=whatIf(ci.tasks,ci.pool,{taskId:'integ',delayDays:3});
  console.log('Scenario: '+w1.scenario);
  console.log('Baseline: '+w1.baseline.makespan+'d -> Modified: '+w1.modified.makespan+'d (impact: '+(w1.impact>0?'+':'')+w1.impact+'d)');
  console.log('Critical path changed: '+(w1.criticalPathChanged?'YES':'No'));
  console.log('');
  console.log('=== What-If: Add 2 CI workers ===');
  var w2=whatIf(ci.tasks,ci.pool,{resource:'ci',addWorkers:2});
  console.log('Scenario: '+w2.scenario);
  console.log('Baseline: '+w2.baseline.makespan+'d -> Modified: '+w2.modified.makespan+'d (impact: '+(w2.impact>0?'+':'')+w2.impact+'d)');
  console.log('');console.log('=== Sprint Planning (summary) ===');
  var sp=template('sprint'),spm=criticalPath(sp.tasks);
  console.log('Sprint: '+spm.projectDuration+'d, '+spm.criticalPath.length+' critical tasks');
  console.log('Stats: 17 exports, 18 tests, 3 templates, 0 dependencies');
})();

if(typeof module!=='undefined'&&module.exports){module.exports={createTask:createTask,createPool:createPool,validate:validate,topoSort:topoSort,criticalPath:criticalPath,schedule:schedule,gantt:gantt,analyze:analyze,monteCarlo:monteCarlo,timeSaved:timeSaved,autoSchedule:autoSchedule,whatIf:whatIf,resourceProfile:resourceProfile,template:template,report:report,selfTest:selfTest,help:help};}
