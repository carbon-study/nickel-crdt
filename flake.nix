{
  description = "nickel-crdt: Rust core and implementation-linked proof scaffolding";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7d1a7c21a4c00ea653fc7ed5c083d261340f185f";
  inputs.hax.url = "github:cryspen/hax/f33e5c844497c057450ebf56828cbb191223e93a";
  # PR affected-set selection only (not wired into CI): the default is a sentinel that always selects the
  # full register gate; a PR build overrides it with the exact base commit, e.g.
  # --override-input selection-base github:carbon-study/nickel-crdt/<base-sha>.
  inputs.selection-base = { url = "path:./nix/selection-base-none"; flake = false; };

  outputs = { self, nixpkgs, hax, selection-base }:
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
        postCheck = ''
          cargo run --offline --locked --example policy-boundary
        '';
      };
      tools = [ pkgs.nodejs_22 pkgs.gnumake pkgs.coreutils pkgs.util-linux rust ];
      # One checked inventory per gate, not all of scripts/. Adding an import
      # requires updating its gate inventory; gate-inputs checks real packages.
      gateScripts = builtins.fromJSON (builtins.readFile ./nix/gate-scripts.json);
      scriptsFor = gate: pkgs.lib.fileset.unions
        (map (name: ./. + "/scripts/${name}") gateScripts.${gate});
      modelEnv = ''
        export NICKEL_PROOF_FSTAR="${fstar}/bin/fstar.exe"
        export NICKEL_HAX_SOURCE="${hax}"
      '';
      proofTools = pkgs.lib.fileset.toSource {
        root = ./scripts;
        fileset = scriptsFor "models";
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
          ./proofs/generated ./proofs/EventGraph.lt ./proofs/EventGraphText.lt ./proofs/EventShell.lt ./proofs/EventClassifier.lt ./proofs/LoopEquality.lt ./proofs/Prelude.lt ./proofs/LoopUtil.lt ./proofs/Vector.lt ./proofs/Smoke.lt ./proofs/EditAtomic.lt ./proofs/EditCommit.lt ./proofs/EditIdentity.lt ./proofs/EditAccepted.lt ./proofs/EditWellFormed.lt ./proofs/Spec.lt ./proofs/EditCausal.lt ./proofs/EditPast.lt ./proofs/EditPastTotal.lt ./proofs/EditSchedule.lt ./proofs/EditBasis.lt ./proofs/EditReplay.lt
          (scriptsFor "text")
        ];
      };
      # One proof derivation per argument list. The full gate (no arguments) stays
      # the local `nix flake check`; CI builds the core and mode shards in parallel.
      proofShards = 3;
      mkProofCheck = name: smoke: args: pkgs.runCommand "nickel-proof-${name}" {
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
        ${pkgs.lib.optionalString smoke ''node scripts/check-proofs.mjs "$out"''}
        node scripts/check-edit-proofs.mjs "$out/edit"${pkgs.lib.optionalString (args != [ ]) " ${pkgs.lib.escapeShellArgs args}"}
      '';
      proofCheck = mkProofCheck "smoke" true [ ];
      # Smoke, the positive chain, every contract family and cache safety, in two
      # roughly equal halves; the second takes every family the first omits.
      proofCoreFamilies = [ "remaining" "spec" "accepted" ];
      proofCoreA = mkProofCheck "core-a" true ([ "cache-safety" ] ++ map (f: "contracts:${f}") proofCoreFamilies);
      proofCoreB = mkProofCheck "core-b" false [ "contracts-except:${builtins.concatStringsSep "," proofCoreFamilies}" ];
      proofShardChecks = builtins.listToAttrs (builtins.genList (i: {
        name = "proofs-shard-${toString i}";
        value = mkProofCheck "shard-${toString i}" false [ "shard:${toString i}/${toString proofShards}" ];
      }) proofShards);
      # Separate experimental implementation controls, not the text proof gate.
      sharedNativeSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [ ./src ./tests/shared_layer.rs
          (scriptsFor "sharedNative") ];
      };
      sharedNative = pkgs.runCommand "nickel-shared-native" {
        nativeBuildInputs = tools;
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        cp -r ${sharedNativeSource} work
        chmod -R u+w work
        cd work
        node scripts/check-shared-native.mjs "$out"
      '';
      sharedProofSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [ ./src/causal.rs ./src/event_layer.rs ./src/event_shell.rs
          ./proofs/CausalEnvelope.lt ./proofs/causal-envelope-view
          ./proofs/Prelude.lt ./proofs/LoopUtil.lt
          ./proofs/generated/Nickel.Prelude.fst ./proofs/generated/Nickel.LoopUtil.fst
          (scriptsFor "shared") ];
      };
      sharedProof = pkgs.runCommand "nickel-shared-proofs" {
        nativeBuildInputs = tools;
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        cp -r ${sharedProofSource} work
        chmod -R u+w work
        cd work
        ${modelEnv}
        export NICKEL_HAX_BIN="${haxBin}/bin/cargo-hax"
        export NICKEL_FSTAR_MODEL_CACHE="${models}"
        node scripts/check-causal-envelope.mjs "$out"
      '';
      # Bounded checkpoint laws, not complete register refinement or SEC.
      registerNativeSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [
          ./Cargo.toml ./Cargo.lock ./proof-smoke ./src
          ./tests/register_checkpoint.rs ./examples/register-checkpoint.rs
          (scriptsFor "registerNative")
        ];
      };
      registerSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [
          ./Cargo.toml ./Cargo.lock ./proof-smoke ./src ./tests/register_checkpoint.rs
          ./proofs/Register.lt ./proofs/RegisterPast.lt ./proofs/RegisterHistory.lt ./proofs/RegisterValid.lt ./proofs/RegisterPublic.lt ./proofs/RegisterFrontier.lt ./proofs/Canonical.lt ./proofs/register-view
          ./proofs/Prelude.lt ./proofs/LoopUtil.lt ./proofs/Vector.lt ./proofs/EventGraph.lt ./proofs/EventClassifier.lt ./proofs/EventShell.lt ./proofs/CausalEnvelope.lt
          ./proofs/generated/Nickel.Prelude.fst ./proofs/generated/Nickel.LoopUtil.fst
          ./proofs/generated/Nickel.Vector.fst ./proofs/generated/Nickel.EventGraph.fst ./proofs/generated/Nickel.EventClassifier.fst
          ./proofs/generated/Nickel.EventShell.fst ./proofs/causal-envelope-view/Nickel.CausalEnvelope.fst
          (scriptsFor "register")
        ];
      };
      registerNative = pkgs.runCommand "nickel-register-native" {
        nativeBuildInputs = tools;
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        cp -r ${registerNativeSource} work
        chmod -R u+w work
        cd work
        node scripts/check-register-native.mjs "$out"
      '';
      # One register proof derivation per argument list. The full gate (no arguments) stays the
      # local `nix flake check`; CI builds the mode shards in parallel, each after its own positive.
      registerShards = 4;
      mkRegisterProof = name: extra: args: pkgs.runCommand "nickel-register-proofs${name}" {
        nativeBuildInputs = tools;
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        cp -r ${registerSource} work
        chmod -R u+w work
        cd work
        ${modelEnv}
        export NICKEL_HAX_BIN="${haxBin}/bin/cargo-hax"
        export NICKEL_FSTAR_MODEL_CACHE="${models}"
${extra}        node scripts/check-register-proofs.mjs "$out"${pkgs.lib.optionalString (args != [ ]) " ${pkgs.lib.escapeShellArgs args}"}
      '';
      registerProof = mkRegisterProof "" "" [ ];
      registerShardChecks = builtins.listToAttrs (builtins.genList (i: {
        name = "register-proofs-shard-${toString i}";
        value = mkRegisterProof "-shard-${toString i}" "" [ "shard:${toString i}/${toString registerShards}" ];
      }) registerShards);
      # Checks the gate's partition and that ci.yml lists exactly register-proofs-shard-0..n-1.
      registerShardCoverage = mkRegisterProof "-shard-coverage" "        export NICKEL_CI_WORKFLOW=${./.github/workflows/ci.yml}\n" [ "shard-coverage:${toString registerShards}" ];
      # Selection boundary (scripts/selection-boundary.mjs): exact head (self.rev) and base
      # (selection-base.rev) trees, each exporting its own plans, the head's selector over both, and
      # full on any doubt. Plan export checks only that the proof tool variables are set, so they are
      # placeholders here and the selection does not build models.
      selectionSource = pkgs.lib.fileset.toSource { root = ./scripts; fileset = scriptsFor "selection"; };
      registerSelection = pkgs.runCommand "nickel-register-selection" {
        nativeBuildInputs = tools ++ [ pkgs.git ];
      } ''
        export HOME="$TMPDIR/home"
        mkdir -p "$HOME"
        export NICKEL_HAX_BIN=unused-by-export NICKEL_PROOF_FSTAR=unused-by-export NICKEL_HAX_SOURCE=unused-by-export NICKEL_FSTAR_MODEL_CACHE=unused-by-export
        node ${selectionSource}/selection-boundary.mjs "$out" ${self} ${selection-base} ${pkgs.lib.escapeShellArg (self.rev or "")} ${pkgs.lib.escapeShellArg (selection-base.rev or "")}
      '';
      # Selected register shards: "full" runs the ordinary shard, "selected" consumes the record (which
      # the runner refuses unless it matches this tree's own plan export); anything else refuses.
      registerSelectedChecks = builtins.listToAttrs (builtins.genList (i: let shardArg = "shard:${toString i}/${toString registerShards}"; in {
        name = "register-proofs-selected-shard-${toString i}";
        value = pkgs.runCommand "nickel-register-proofs-selected-shard-${toString i}" {
          nativeBuildInputs = tools;
        } ''
          export HOME="$TMPDIR/home"
          mkdir -p "$HOME"
          cp -r ${registerSource} work
          chmod -R u+w work
          cd work
          ${modelEnv}
          export NICKEL_HAX_BIN="${haxBin}/bin/cargo-hax"
          export NICKEL_FSTAR_MODEL_CACHE="${models}"
          mode="$(cat ${registerSelection}/mode)"
          case "$mode" in
            full) node scripts/check-register-proofs.mjs "$out" ${shardArg} ;;
            selected) node scripts/check-register-proofs.mjs "$out" "selection:${registerSelection}/selection.json" ${shardArg} ;;
            *) echo "unknown selection mode: $mode" >&2; exit 1 ;;
          esac
          cp ${registerSelection}/identity.json "$out/selection-identity.json"
        '';
      }) registerShards);
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
      gateInputSource = pkgs.lib.fileset.toSource {
        root = ./.;
        fileset = pkgs.lib.fileset.unions [ ./scripts ./nix/gate-scripts.json ];
      };
      gateInputs = pkgs.runCommand "nickel-gate-inputs" {
        nativeBuildInputs = [ pkgs.nodejs_22 ];
      } ''
        node --experimental-vm-modules ${gateInputSource}/scripts/check-gate-inputs.mjs \
          text=${proofSource}/scripts shared=${sharedProofSource}/scripts \
          sharedNative=${sharedNativeSource}/scripts models=${proofTools} \
          registerNative=${registerNativeSource}/scripts register=${registerSource}/scripts selection=${selectionSource} > "$out"
      '';
    in {
      packages.${system} = {
        default = native;
        inherit native;
        shared-native = sharedNative;
        shared-proofs = sharedProof;
        register-native = registerNative;
        register-proofs = registerProof;
        edit-reference = editReference;
        proof-models = models;
        gate-inputs = gateInputs;
        proofs = proofCheck;
        proofs-core-a = proofCoreA;
        proofs-core-b = proofCoreB;
        hax = haxBin;
        hax-fstar = fstar;
        register-proofs-shard-coverage = registerShardCoverage;
        register-selection = registerSelection;
      } // proofShardChecks // registerShardChecks // registerSelectedChecks;
      checks.${system} = { inherit native; gate-inputs = gateInputs; register-native = registerNative; register-proofs = registerProof; shared-native = sharedNative; shared-proofs = sharedProof; proofs = proofCheck; edit-reference = editReference; };
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
