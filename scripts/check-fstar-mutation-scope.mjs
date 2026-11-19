import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {fstarDeclaration,replaceUniqueInFstarDeclaration} from './fstar-mutation-scope.mjs';

export function checkFstarMutationScope() {
  const source='module Fixture\nlet owner () =\n  required ();\nlet later () =\n  required ();\n';
  assert.equal(replaceUniqueInFstarDeclaration(source,'owner','required ();','();'),source.replace('required ();','();'));
  assert.equal(fstarDeclaration(source,'owner').body,'let owner () =\n  required ();');
  assert.throws(()=>fstarDeclaration(source,'absent'),/one F\* declaration/);
  assert.throws(()=>fstarDeclaration(source+'let owner () = ()\n','owner'),/one F\* declaration/);
  assert.throws(()=>fstarDeclaration(source,'owner.*'),/unsupported declaration name/);
  assert.throws(()=>replaceUniqueInFstarDeclaration(source,'owner','absent ();','();'),/anchor not found/);
  assert.throws(()=>replaceUniqueInFstarDeclaration(source.replace('  required ();','  ();'),'owner','required ();','();'),/anchor not found/);
  assert.throws(()=>replaceUniqueInFstarDeclaration(source.replace('  required ();','  required (); required ();'),'owner','required ();','();'),/anchor must be unique/);
  assert.throws(()=>replaceUniqueInFstarDeclaration(source,'owner','','();'),/nonempty anchor/);
  assert.throws(()=>replaceUniqueInFstarDeclaration(source,'owner','required ();','required ();'),/changed replacement/);
  // Every supported top-level boundary ends the scope; local lets stay inside.
  for(const next of ['let rec later () = ()','open Aux','type t = unit','module Aux = A','val later: unit','assume val later: unit','unfold let later = ()','and later () = ()']) {
    const input='let owner () =\n  required ();\n'+next+'\n';
    assert.equal(fstarDeclaration(input,'owner').body,'let owner () =\n  required ();');
  }
  assert.throws(()=>fstarDeclaration('let owner () = ()\nexception Unhandled\nlet next () = ()\n','owner'),/unsupported unindented syntax/);
  // Never silently truncate an enumeration at unsupported body directives.
  for(const directive of ['#push-options "--fuel 0"','[@@ inline_for_extraction]']) {
    for(const prefix of ['', '  required ();\n']) {
      const input='let owner () =\n'+prefix+directive+'\n  required ();\nlet later () = ()\n';
      assert.throws(()=>fstarDeclaration(input,'owner'),/unsupported unindented syntax/);
      assert.throws(()=>replaceUniqueInFstarDeclaration(input,'owner','required ();','();'),/unsupported unindented syntax/);
    }
  }
  const local='let rec owner\n  () =\n  let local = "let owner () = ()" in\n  required ();\nlet owner_more = ()\n';
  assert(fstarDeclaration(local,'owner').body.includes('let local'));
  const commented='// let owner () = ()\n(* outer (* let owner () = () *) *)\n'+source;
  assert.equal(fstarDeclaration(commented,'owner').body,fstarDeclaration(source,'owner').body);
  const commentAnchor='let owner () =\n  // required ();\n  ()\n';
  assert.throws(()=>replaceUniqueInFstarDeclaration(commentAnchor,'owner','required ();','();'),/anchor must start in code/);
  assert.throws(()=>fstarDeclaration('(* incomplete\n'+source,'owner'),/unterminated F\* comment/);
  assert.throws(()=>fstarDeclaration('let other = "incomplete\n'+source,'owner'),/unterminated F\* string/);
  const unicode='(* 🦉 *)\n'+source;
  assert.equal(replaceUniqueInFstarDeclaration(unicode,'owner','required ();','();'),unicode.replace('required ();','();'));
  console.log('PASS F* mutation scope: unique declarations/anchors, boundaries, comments, UTF-16 offsets and refusal controls');
}

if(process.argv[1]===fileURLToPath(import.meta.url))checkFstarMutationScope();
