// Prepare a Latte MCP "hax lane" (strict native queries) for the text client.
// Run inside Nickel's locked dev shell (it provides NICKEL_HAX_BIN/NICKEL_HAX_SOURCE).
//
//   LATTE_ROOT=/abs/latte-nursery  CAPTURE_DIR=/abs/new-dir  node scripts/latte-hax-lane.mjs
//
// It freshly extracts the text client with the exact production hax arguments of
// scripts/check-edit-proofs.mjs, refuses unless the three modules are byte-identical
// to proofs/generated/hax/, writes a receipt, generates the Latte hax project manifest
// over (hax proof-libs, hax extraction models, this native capsule) and prints the MCP
// launch line. It changes no tracked file. A mismatch is a blocker: never refresh the
// tracked snapshots from here. The manifest names captured bytes, not live Rust; after
// any native edit, run this again into a new CAPTURE_DIR and start a new connection.
// Requires Latte's own `.#hax-fstar` runtime (F* 2025.10.06, commit 7b347386...):
// Nickel's bare upstream F* package reports `~dev` and the hax lane refuses it.
import fs from 'node:fs';import path from 'node:path';import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';import assert from 'node:assert/strict';
const env=process.env;
const root=fs.realpathSync(env.NICKEL_ROOT||process.cwd());
for(const name of ['LATTE_ROOT','CAPTURE_DIR','NICKEL_HAX_BIN','NICKEL_HAX_SOURCE'])assert(env[name],`set ${name}`);
const latteRoot=fs.realpathSync(env.LATTE_ROOT),dir=env.CAPTURE_DIR;
assert(path.isAbsolute(dir),'CAPTURE_DIR must be absolute');
fs.mkdirSync(dir); // refuse an existing capture generation
const capsule=path.join(dir,'native');fs.mkdirSync(capsule);
const run=(cmd,args,opts={})=>{const r=spawnSync(cmd,args,{encoding:'utf8',...opts});return r;};

// 1. Runtime identity: Latte's declared hax-fstar, never a wrapper or the bare package.
const built=run('nix',['build','--no-link','--print-out-paths',`${latteRoot}#hax-fstar`]);
assert.equal(built.status,0,'building Latte .#hax-fstar failed:\n'+built.stderr);
const fstar=path.join(built.stdout.trim().split('\n').pop(),'bin/fstar.exe');
const version=run(fstar,['--version']).stdout;
assert.match(version,/F\* 2025\.10\.06/);assert.match(version,/commit=7b347386330d0e5a331a220535b6f15288903234/);

// 2. Fresh production extraction, compared byte-for-byte with the tracked snapshot.
const source=fs.readFileSync(path.join(root,'scripts/check-edit-proofs.mjs'),'utf8');
const line=source.split('\n').find(x=>x.startsWith('const haxArgs=out=>'));
assert(line,'production hax argument definition (const haxArgs=out=>...) missing');
const args=new Function('out','return '+line.slice('const haxArgs=out=>'.length,-1))(capsule);
const extraction=run(env.NICKEL_HAX_BIN,args,{cwd:root,env:{...env,CARGO_TARGET_DIR:capsule+'-target'}});
fs.writeFileSync(path.join(dir,'extraction.log'),(extraction.stdout||'')+(extraction.stderr||''));
assert.equal(extraction.status,0,'production extraction failed; see extraction.log');
const names=fs.readdirSync(capsule).sort();
assert.deepEqual(names,['Nickel_crdt.Edit.fst','Nickel_crdt.Event_layer.fst','Nickel_crdt.Event_shell.fst']);
const sha=p=>createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const receipt={root,head:run('git',['rev-parse','HEAD'],{cwd:root}).stdout.trim(),productionArguments:args,fstar,native:{},source:{}};
for(const n of names){
  assert(fs.readFileSync(path.join(capsule,n)).equals(fs.readFileSync(path.join(root,'proofs/generated/hax',n))),
    'fresh extraction differs from proofs/generated/hax/'+n+' (blocker; do not refresh snapshots here)');
  receipt.native[n]=sha(path.join(capsule,n));
}
for(const n of ['Cargo.toml','Cargo.lock','src/edit.rs','src/event_layer.rs','src/event_shell.rs','scripts/check-edit-proofs.mjs','proofs/latte.modules.json'])
  receipt.source[n]=sha(path.join(root,n));
fs.writeFileSync(path.join(dir,'receipt.json'),JSON.stringify(receipt,null,2)+'\n');

// 3. Manifest: only the hax model roots and this native capsule. Do not add
// proofs/generated or proofs/register-view wholesale: their authored modules
// collide with the workspace's own sources.
const cli=run('nix',['build','--no-link','--print-out-paths',`${latteRoot}#cli`]);
assert.equal(cli.status,0,'building Latte .#cli failed:\n'+cli.stderr);
const latte=path.join(cli.stdout.trim().split('\n').pop(),'bin/latte');
const hs=env.NICKEL_HAX_SOURCE;
const manifest=run(latte,['hax-project','--root',`${hs}/hax-lib/proof-libs/fstar`,'--root',`${hs}/hax-lib/proofs/fstar/extraction`,'--root',capsule,'--verify','Nickel_crdt.Edit']);
assert.equal(manifest.status,0,'latte hax-project failed:\n'+manifest.stderr);
const project=path.join(dir,'text.hax.json');fs.writeFileSync(project,manifest.stdout);

const mcp=path.join(latteRoot,'apps/mcp/dist/latte-mcp.cjs');
console.log('PASS fresh production extraction equals proofs/generated/hax; manifest written');
console.log('MCP launch (NIX_REMOTE=daemon; requires a built latte-mcp at the same Latte revision):');
console.log([process.execPath,mcp,'--stdio','--root',path.join(root,'proofs'),'--target','hax','--project',project,'--fstar',fstar].join(' '));
