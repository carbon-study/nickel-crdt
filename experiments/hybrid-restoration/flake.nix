{
  description = "Directed observed-concurrent restoration reference candidate";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7d1a7c21a4c00ea653fc7ed5c083d261340f185f";
  outputs = {self, nixpkgs}: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {inherit system;};
    source = pkgs.lib.fileset.toSource { root = ./.; fileset = pkgs.lib.fileset.unions [./model.py ./check.py ./sessions.py ./session_check.py ./continuation_check.py]; };
    check = pkgs.runCommand "hybrid-restoration-directed-check" {nativeBuildInputs=[pkgs.python3];} ''
      export PYTHONDONTWRITEBYTECODE=1
      python ${source}/check.py
      python ${source}/session_check.py
      python ${source}/continuation_check.py > continuation-output.json
      cmp continuation-output.json ${./continuation-output.json}
      for mode in drop-redo drop-ignored reset-counter; do
        if python ${source}/continuation_check.py "$mode" > "$mode.json"; then
          echo "cold-session mutation unexpectedly passed: $mode"; exit 1
        fi
        grep -q 'cold continuation mismatch' "$mode.json"
        cmp "$mode.json" ${./continuation-controls}/"$mode.json"
      done
      python ${source}/session_check.py trace > session-trace.json
      cmp session-trace.json ${./session-trace.json}
      (cd ${source}; python -O -c 'from check import admission_checks; admission_checks()')
      if python ${source}/check.py target-only > target-only.log 2>&1; then
        echo 'target-only mutation unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: q07 observed concurrent deletes' target-only.log
      if python ${source}/check.py all-known > all-known.log 2>&1; then
        echo 'all-known mutation unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: later deletion remains through author undo' all-known.log
      if python ${source}/check.py legacy-hide > legacy-hide.log 2>&1; then
        echo 'legacy creator-hide policy unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: creator withdrawal survives peer deletion undo' legacy-hide.log
      if python ${source}/check.py spill > spill.log 2>&1; then
        echo 'scope-spill mutation unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: overlap restoration stays in selected scope' spill.log
      if python ${source}/check.py split-undo > split-undo.log 2>&1; then
        echo 'split undo unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: half-published compound undo' split-undo.log
      if python ${source}/session_check.py consume > consumed-skip.log 2>&1; then
        echo 'consumed-skip alternative unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: skipped deletion must reactivate after peer redo' consumed-skip.log
      touch $out
    '';
    run = pkgs.writeShellApplication { name="hybrid-restoration"; runtimeInputs=[pkgs.python3]; text=''export PYTHONDONTWRITEBYTECODE=1; exec python ${source}/check.py "$@"''; };
  in {
    checks.${system}.default = check;
    apps.${system} = {
    continuations = let continuationRun = pkgs.writeShellApplication {
      name="hybrid-continuations"; runtimeInputs=[pkgs.python3];
      text=''export PYTHONDONTWRITEBYTECODE=1; exec python ${source}/continuation_check.py "$@"'';
    }; in {type="app"; program="${continuationRun}/bin/hybrid-continuations"; meta.description="Bounded cold-session continuation comparisons";};
    sessions = let sessionRun = pkgs.writeShellApplication {
      name="hybrid-sessions"; runtimeInputs=[pkgs.python3];
      text=''export PYTHONDONTWRITEBYTECODE=1; exec python ${source}/session_check.py "$@"'';
    }; in {type="app"; program="${sessionRun}/bin/hybrid-sessions"; meta.description="Replay generated private-session actions";};
    default = {type="app"; program="${run}/bin/hybrid-restoration"; meta.description="Replay directed restoration candidate fixtures";};
    };
    devShells.${system}.default=pkgs.mkShell {packages=[pkgs.python3];};
  };
}
