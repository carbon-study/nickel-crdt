// Parse gate modules without evaluating them; audit the exact packaged scripts.
// Dynamic imports deliberately support only the literal forms used by the gates.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import path from 'node:path';
import vm from 'node:vm';
import {isBuiltin} from 'node:module';
import {fileURLToPath} from 'node:url';
const root = fileURLToPath(new URL('..', import.meta.url));
export const entries = {
  text: ['check-edit-proofs.mjs', 'check-proofs.mjs'],
  shared: ['check-causal-envelope.mjs'],
  sharedNative: ['check-shared-native.mjs'],
  models: ['build-proof-models.mjs'],
  registerNative: ['check-register-native.mjs'],
  register: ['check-register-proofs.mjs'],
};
export function dependencies(source, name) {
  const specs = [...new vm.SourceTextModule(source, {identifier:name}).dependencySpecifiers];
  // Conservative: also finds apparent imports in comments/strings. Unsupported
  // forms refuse rather than silently missing a runtime dependency.
  const dynamic = /\bimport(?:(?:\s+)|(?:\/\/[^\r\n\u2028\u2029]*[\r\n\u2028\u2029])|(?:\/\*[\s\S]*?\*\/))*\(/g;
  for (const m of source.matchAll(dynamic)) {
    const literal = /^\s*(['"])([^'"\\\r\n]+)\1\s*\)/.exec(source.slice(m.index+m[0].length));
    assert(literal, name+': unsupported dynamic import; use a plain literal');
    specs.push(literal[2]);
  }
  return [...new Set(specs.filter(s=>!isBuiltin(s)).map(s=>{
    assert(/^\.\/[a-z0-9-]+\.mjs$/.test(s), name+': unsupported non-builtin dependency '+s);
    return s.slice(2);
  }))].sort();
}
export async function closure(seeds, read) {
  const found=new Set(), pending=[...seeds];
  while(pending.length) {
    const name=pending.pop(); if(found.has(name))continue;
    found.add(name); pending.push(...dependencies(await read(name),name));
  }
  return [...found].sort();
}
function sameFiles(actual,expected,label){assert.deepEqual(actual,expected,label);}
function sameBytes(actual,expected,label){assert.deepEqual(actual,expected,label);}
async function controls() {
  const fixture=new Map([['entry.mjs',"import './child.mjs';"],['child.mjs',"export const x=1;"]]);
  const read=async name=>{assert(fixture.has(name),'missing '+name);return fixture.get(name);};
  const wanted=await closure(['entry.mjs'],read);
  assert.deepEqual(wanted,['child.mjs','entry.mjs']);
  assert.throws(()=>sameFiles(['entry.mjs'],wanted,'omitted dependency'),/omitted dependency/);
  assert.throws(()=>sameFiles([...wanted,'extra.mjs'].sort(),wanted,'extra script'),/extra script/);
  fixture.set('entry.mjs',"export * from './child.mjs'; await import('./later.mjs');");
  await assert.rejects(()=>closure(['entry.mjs'],read),/missing later/);
  fixture.set('later.mjs','export const y=2;');
  assert.deepEqual(await closure(['entry.mjs'],read),['child.mjs','entry.mjs','later.mjs']);
  assert.deepEqual(dependencies("await import /* note */ ('./child.mjs');",'fixture'),['child.mjs']);
  for(const end of ['\n','\r','\r\n','\u2028','\u2029']) {
    assert.deepEqual(dependencies('await import // note'+end+"('./child.mjs');",'fixture'),['child.mjs']);
    assert.throws(()=>dependencies('await import // note'+end+'(name);','fixture'),/unsupported dynamic import/);
  }
  assert.throws(()=>sameBytes(Buffer.from('// \ufffd\n'),Buffer.from([47,47,32,255,10]),'changed bytes'),/changed bytes/);
  sameBytes(Buffer.from('// equal\n'),Buffer.from('// equal\n'),'equal bytes');
  assert.throws(()=>dependencies('await import(name);','fixture'),/unsupported dynamic import/);
  assert.throws(()=>dependencies("await import('./' + name);",'fixture'),/unsupported dynamic import/);
  assert.throws(()=>dependencies("import '../escape.mjs';",'fixture'),/unsupported non-builtin/);
  assert.deepEqual(dependencies("import fs from 'node:fs'; const text=\"import './ghost.mjs';\";",'fixture'),[]);
  assert.throws(()=>dependencies('import {','fixture'),SyntaxError);
}
export async function check(rootDir, manifest, packaged={}) {
  assert.deepEqual(Object.keys(manifest).sort(),Object.keys(entries).sort(),'gate manifest keys');
  const result={};
  for(const [gate,seeds] of Object.entries(entries)) {
    const files=manifest[gate];assert(Array.isArray(files)&&files.every(f=>/^[a-z0-9-]+\.mjs$/.test(f)),gate+' script names');
    assert.deepEqual(files,[...new Set(files)].sort(),gate+' sorted unique files');
    const actual=await closure(seeds,name=>fs.readFile(path.join(rootDir,'scripts',name),'utf8'));
    sameFiles(files,actual,gate+' must contain exactly its transitive import closure');
    if(packaged[gate]) {
      const names=(await fs.readdir(packaged[gate])).sort();
      sameFiles(names,files,gate+' actual Nix-packaged inventory');
      for(const name of files)sameBytes(await fs.readFile(path.join(packaged[gate],name)),await fs.readFile(path.join(rootDir,'scripts',name)),gate+' packaged bytes: '+name);
    }
    result[gate]=files;
  }
  return result;
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  await controls();
  const manifest=JSON.parse(await fs.readFile(path.join(root,'nix/gate-scripts.json'),'utf8'));
  const packaged=Object.fromEntries(process.argv.slice(2).map(arg=>{const i=arg.indexOf('=');assert(i>0,'use gate=packaged-directory');return [arg.slice(0,i),arg.slice(i+1)];}));
  for(const name of Object.keys(packaged))assert(Object.hasOwn(entries,name),'unknown packaged gate '+name);
  if(Object.keys(packaged).length)assert.deepEqual(Object.keys(packaged).sort(),Object.keys(entries).sort(),'supply every packaged gate');
  console.log(JSON.stringify(await check(root,manifest,packaged),null,2));
  console.log('PASS gate import closures, packaged inventories/bytes and omission/extra/dynamic-import controls');
}
