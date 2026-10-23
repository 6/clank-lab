// Independent JavaScript implementation; edges are keyed by exact labels.
const fs=require('fs'),zlib=require('zlib');
try {
 const g=JSON.parse(fs.readFileSync(process.argv[2]));
 let b=fs.readFileSync(process.argv[3]);if(process.argv[3].endsWith('.gz'))b=zlib.gunzipSync(b);
 const c=JSON.parse(b),key=x=>JSON.stringify(x),fail=s=>{throw Error(s)};
 if(c.group!==g.group)fail('wrong group');
 const ranks=new Map(),counts=new Map(),edges=new Set();
 g.labels.forEach((v,i)=>{let k=key(v);if(ranks.has(k))fail('duplicate source');ranks.set(k,g.ranks[i]);counts.set(k,0)});
 g.edges.forEach(e=>edges.add(key([g.labels[e[0]-1],g.labels[e[1]-1]])));
 for(const ch of c.chains){
  if(!ch.length)fail('empty');
  if(ranks.get(key(ch[0]))+ranks.get(key(ch[ch.length-1]))!==g.rank)fail('not symmetric');
  for(let i=0;i<ch.length;i++){
   let k=key(ch[i]);if(!counts.has(k))fail('unknown element');counts.set(k,counts.get(k)+1);
   if(i && (ranks.get(k)!==ranks.get(key(ch[i-1]))+1 || !edges.has(key([ch[i-1],ch[i]]))))fail('not saturated');
  }
 }
 if([...counts.values()].some(x=>x!==1))fail('not a partition');
 console.log(JSON.stringify({accepted:true,checker:'javascript',vertices:g.labels.length,chains:c.chains.length,rank_sizes:Array.from({length:g.rank+1},(_,i)=>g.ranks.filter(x=>x===i).length)}));
}catch(e){console.log('REJECT '+e.message);process.exit(1)}
