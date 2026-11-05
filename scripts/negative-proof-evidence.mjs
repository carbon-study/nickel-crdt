import path from 'node:path';

// Tie an ordinary failed query to a terminal semantic error in the unchanged
// theorem's generated declaration. A failed preliminary query is not enough.
export function hasOrdinaryTheoremRejection({status,log,theorem,view}) {
  if(status!==2||typeof view!=='string'||typeof log!=='string')return false;
  const pieces=theorem.split('.'),name=pieces.pop(),file=pieces.join('.')+'.fst';
  const source=view.split('\n'),starts=[];
  for(let i=0;i<source.length;i++) {
    const match=/^let(?: rec)?\s+([\w']+)(?=\s|\(|:)/.exec(source[i]);
    if(match?.[1]===name)starts.push(i);
  }
  if(starts.length!==1)return false;
  const start=starts[0]+1;
  let end=source.length;
  for(let i=start;i<source.length;i++)if(/^(?:let|type|val|module|open)\b/.test(source[i])){end=i;break;}
  const inside=(f,a,b)=>path.basename(f)===file&&a>=start&&b>=a&&b<=end;
  const lines=log.split('\n');
  const attempts=lines.map(line=>({line,match:/^\(([^()]+)\((\d+),(\d+)-(\d+),(\d+)\)\)\s+Query-stats \(([^,]+), \d+\)\s+(succeeded|failed)\b/.exec(line)}))
    .filter(x=>x.match?.[6]===theorem);
  const last=attempts.at(-1);
  if(!last||last.match[7]!=='failed')return false;
  const [,queryFile,a,ac,b,bc]=last.match,first=Number(a),finish=Number(b);
  if(!inside(queryFile,first,finish))return false;
  if(/reason-unknown=[^}]*?(?:canceled|resource limits reached|timeout)/i.test(last.line))return false;
  const budget=/and rlimit (\d+) \(used rlimit ([\d.]+)\)/.exec(last.line);
  if(!budget||!(Number(budget[2])<Number(budget[1])))return false;
  for(let i=0;i<lines.length;i++) {
    const error=/^\* Error (\d+) at ([^(]+)\((\d+),(\d+)-(\d+),(\d+)\):$/.exec(lines[i]);
    if(!error)continue;
    const [,code,errorFile,c,cc,d,dc]=error,lo=Number(c),hi=Number(d);
    const before=(x,y)=>x[0]<y[0]||(x[0]===y[0]&&x[1]<y[1]);
    if(!inside(errorFile,lo,hi)||before([hi,Number(dc)],[first,Number(ac)])||before([finish,Number(bc)],[lo,Number(cc)]))continue;
    const body=[];
    for(let j=i+1;j<lines.length&&lines[j].trim()&&!lines[j].startsWith('* ');j++)body.push(lines[j]);
    const message=body.join('\n');
    if(code==='19'&&/Could not prove post-condition|Assertion failed/.test(message))return true;
    if(code==='228'&&/Tactic failed/.test(message)&&/SMT did not solve this goal/.test(message))return true;
  }
  return false;
}
