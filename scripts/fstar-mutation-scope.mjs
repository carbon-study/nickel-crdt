// Deliberately bounded to the line-oriented declarations emitted by our pinned
// producer. This is a mutation locator, not an F* parser or proof classifier.
import assert from 'node:assert/strict';

// Preserve offsets/newlines while excluding strings and nested F* comments from
// declaration discovery. Apostrophes are identifier characters, not Rust chars.
function declarationCode(source) {
  const out=source.split('');
  let block=0,string=false,line=false;
  for(let i=0;i<source.length;i++) {
    const c=source[i],n=source[i+1];
    if(line) { if(c==='\n')line=false;else out[i]=' ';continue; }
    if(block) {
      if(c==='('&&n==='*'){out[i]=out[i+1]=' ';block++;i++;}
      else if(c==='*'&&n===')'){out[i]=out[i+1]=' ';block--;i++;}
      else if(c!=='\n'&&c!=='\r')out[i]=' ';
      continue;
    }
    if(string) {
      if(c!=='\n'&&c!=='\r')out[i]=' ';
      if(c==='\\'&&i+1<source.length){if(n!=='\n'&&n!=='\r')out[i+1]=' ';i++;}
      else if(c==='"')string=false;
      continue;
    }
    if(c==='/'&&n==='/'){out[i]=out[i+1]=' ';line=true;i++;}
    else if(c==='('&&n==='*'){out[i]=out[i+1]=' ';block=1;i++;}
    else if(c==='"'){out[i]=' ';string=true;}
  }
  assert.equal(block,0,'unterminated F* comment');
  assert(!string,'unterminated F* string');
  return out.join('');
}

export function fstarDeclaration(source,name,where=name) {
  assert(/^[A-Za-z_][A-Za-z0-9_']*$/.test(name),`${where}: unsupported declaration name`);
  const code=declarationCode(source);
  const matches=[...code.matchAll(new RegExp('^let (?:rec )?'+name+'(?=[ \\t\\r\\n])','gm'))];
  assert.equal(matches.length,1,`${where}: one F* declaration required: ${name}`);
  const start=matches[0].index,tail=code.slice(start+matches[0][0].length);
  // Stop before another top-level declaration/directive, including modifiers
  // used by emitted definitions. Indented local lets are part of the owner.
  const next=/\n(?:(?:(?:unfold|inline_for_extraction|noextract|irreducible|private) )*(?:let|type|val|assume val|open|module|and)\b|#|\[@)/.exec(tail);
  const end=next?start+matches[0][0].length+next.index:source.length;
  const unsupported=code.slice(start,end).split('\n').slice(1).find(line=>line.length&&!/^[ \t\r]/.test(line)&&!/^else\b/.test(line));
  assert(!unsupported,`${where}: unsupported unindented syntax inside declaration`);
  return {start,end,body:source.slice(start,end)};
}

export function replaceUniqueInFstarDeclaration(source,name,needle,replacement,where=name) {
  assert(typeof needle==='string'&&needle.length>0,`${where}: nonempty anchor required`);
  assert(typeof replacement==='string'&&needle!==replacement,`${where}: changed replacement required`);
  const {start,end,body}=fstarDeclaration(source,name,where);
  const at=body.indexOf(needle);
  assert(at>=0,`${where}: anchor not found in declaration ${name}`);
  const significant=needle.search(/\S/);
  assert(significant>=0&&declarationCode(source)[start+at+significant]===needle[significant],`${where}: anchor must start in code`);
  assert.equal(body.indexOf(needle,at+1),-1,`${where}: anchor must be unique in declaration ${name}`);
  return source.slice(0,start+at)+replacement+source.slice(start+at+needle.length);
}
