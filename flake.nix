{
  description = "nickel-crdt: Rust core and implementation-linked proof scaffolding";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7d1a7c21a4c00ea653fc7ed5c083d261340f185f";
  inputs.hax.url = "github:cryspen/hax/f33e5c844497c057450ebf56828cbb191223e93a";

  outputs = { self, nixpkgs, hax }:
    nixpkgs.lib.foldl' nixpkgs.lib.recursiveUpdate { } (map (system: let
      pkgs = import nixpkgs { inherit system; };
      rust = hax.packages.${system}.rustc;
      haxBin = hax.packages.${system}.default;
      fstar = hax.inputs.fstar.packages.${system}.default;
      rustPlatform = pkgs.makeRustPlatform { cargo = rust; rustc = rust; };
      rustSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [ ./Cargo.toml ./Cargo.lock ./src ./tests ./examples ./proof-smoke ];
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
        fileset = pkgs.lib.fileset.unions [ ./scripts/build-proof-models.mjs ./scripts/proof-cache.mjs ./scripts/check-proof-timeouts.mjs ];
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
          ./Cargo.toml ./Cargo.lock ./src ./tests ./proof-smoke
          ./proofs/generated ./proofs/Prelude.lt ./proofs/LoopUtil.lt ./proofs/Smoke.lt ./proofs/EditAtomic.lt ./proofs/EditCommit.lt ./proofs/EditIdentity.lt ./proofs/EditAccepted.lt ./proofs/EditWellFormed.lt ./proofs/EditCausal.lt ./scripts
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
        node scripts/check-edit-proofs.mjs "$out/edit"
      '';
      editReferenceSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [
          ./Cargo.toml ./Cargo.lock ./src ./examples ./proof-smoke
          ./scripts/check-rust-edit-reference.py
          ./experiments/combined-admission ./experiments/hybrid-restoration
          ./experiments/ordered-gap-reference
        ];
      };
      editReference = pkgs.runCommand "nickel-edit-reference" {
        nativeBuildInputs = tools ++ [ pkgs.python3 ];
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME" "$out"
        cp -r ${editReferenceSource} work
        chmod -R u+w work
        cd work
        cargo run --offline --locked --quiet --example edit-reference > "$out/fixtures.json"
        export NODE="${pkgs.nodejs_22}/bin/node"
        python3 scripts/check-rust-edit-reference.py "$out/fixtures.json" > "$out/receipt.json"
        cat "$out/receipt.json"
      '';
    in {
      packages.${system} = {
        default = native;
        inherit native;
        edit-reference = editReference;
        proof-models = models;
        proofs = proofCheck;
        hax = haxBin;
        hax-fstar = fstar;
      };
      checks.${system} = { inherit native; proofs = proofCheck; edit-reference = editReference; };
      devShells.${system} = {
        default = pkgs.mkShell {
          packages = tools ++ [ haxBin fstar ];
        };
        # Reference gates use Node; Python stays in its owning nested flake.
        # Do not realize hax/F*/Rust just to run these scripts or compare JSON.
        references = pkgs.mkShell {
          packages = [ pkgs.nodejs_22 pkgs.jq pkgs.coreutils pkgs.util-linux ];
        };
      };
    }) [ "x86_64-linux" "aarch64-linux" ]);
}
