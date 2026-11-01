{
  description = "Directed observed-concurrent restoration reference candidate";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7d1a7c21a4c00ea653fc7ed5c083d261340f185f";
  outputs = {self, nixpkgs}: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {inherit system;};
    source = pkgs.lib.fileset.toSource { root = ./.; fileset = pkgs.lib.fileset.unions [./model.py ./check.py]; };
    check = pkgs.runCommand "hybrid-restoration-directed-check" {nativeBuildInputs=[pkgs.python3];} ''
      export PYTHONDONTWRITEBYTECODE=1
      python ${source}/check.py
      if python ${source}/check.py target-only > target-only.log 2>&1; then
        echo 'target-only mutation unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: q07 observed concurrent deletes' target-only.log
      if python ${source}/check.py all-known > all-known.log 2>&1; then
        echo 'all-known mutation unexpectedly passed'; exit 1
      fi
      grep -q 'AssertionError: later deletion remains through author undo' all-known.log
      touch $out
    '';
    run = pkgs.writeShellApplication { name="hybrid-restoration"; runtimeInputs=[pkgs.python3]; text=''export PYTHONDONTWRITEBYTECODE=1; exec python ${source}/check.py "$@"''; };
  in {
    checks.${system}.default = check;
    apps.${system}.default = {type="app"; program="${run}/bin/hybrid-restoration"; meta.description="Replay directed restoration candidate fixtures";};
    devShells.${system}.default=pkgs.mkShell {packages=[pkgs.python3];};
  };
}
