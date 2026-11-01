{
  description = "nickel-crdt: Rust core and implementation-linked proof scaffolding";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7d1a7c21a4c00ea653fc7ed5c083d261340f185f";
  inputs.hax.url = "github:cryspen/hax/f33e5c844497c057450ebf56828cbb191223e93a";

  outputs = { self, nixpkgs, hax }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      rust = hax.packages.${system}.rustc;
      haxBin = hax.packages.${system}.default;
      fstar = hax.inputs.fstar.packages.${system}.default;
      rustPlatform = pkgs.makeRustPlatform { cargo = rust; rustc = rust; };
      rustSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [ ./Cargo.toml ./Cargo.lock ./src ./proof-smoke ];
      };
      native = rustPlatform.buildRustPackage {
        pname = "nickel-crdt";
        version = "0.0.0";
        src = rustSource;
        cargoLock.lockFile = ./Cargo.lock;
        cargoBuildFlags = [ "--workspace" ];
        cargoTestFlags = [ "--workspace" ];
      };
      tools = [ pkgs.nodejs_22 pkgs.gnumake pkgs.coreutils pkgs.util-linux rust ];
      modelEnv = ''
        export NICKEL_PROOF_FSTAR="${fstar}/bin/fstar.exe"
        export NICKEL_HAX_SOURCE="${hax}"
      '';
      proofTools = pkgs.lib.fileset.toSource {
        root = ./scripts;
        fileset = pkgs.lib.fileset.unions [ ./scripts/build-proof-models.mjs ./scripts/proof-cache.mjs ];
      };
      models = pkgs.runCommand "nickel-checked-hax-models" {
        nativeBuildInputs = tools;
      } ''
        ${modelEnv}
        node ${proofTools}/build-proof-models.mjs "$out"
      '';
      proofSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [
          ./Cargo.toml ./Cargo.lock ./src ./proof-smoke
          ./proofs/generated ./proofs/Prelude.lt ./proofs/LoopUtil.lt ./proofs/Smoke.lt ./scripts
        ];
      };
      proofCheck = pkgs.runCommand "nickel-proof-smoke" {
        nativeBuildInputs = tools;
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        cp -r ${proofSource} work
        chmod -R u+w work
        cd work
        ${modelEnv}
        export NICKEL_HAX_BIN="${haxBin}/bin/cargo-hax"
        export NICKEL_FSTAR_MODEL_CACHE="${models}"
        node scripts/check-proofs.mjs "$out"
      '';
    in {
      packages.${system} = {
        default = native;
        inherit native;
        proof-models = models;
        proofs = proofCheck;
        hax = haxBin;
        hax-fstar = fstar;
      };
      checks.${system} = { inherit native; proofs = proofCheck; };
      devShells.${system}.default = pkgs.mkShell {
        packages = tools ++ [ haxBin fstar ];
      };
    };
}
