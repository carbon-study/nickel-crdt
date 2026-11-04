{
  description = "Nickel undo-semantics questionnaire: local answers and portable JSON export";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/7d1a7c21a4c00ea653fc7ed5c083d261340f185f";
  outputs = { self, nixpkgs }:
    nixpkgs.lib.foldl' nixpkgs.lib.recursiveUpdate { } (map (system: let
      pkgs = import nixpkgs { inherit system; };
      site = pkgs.runCommand "nickel-undo-questionnaire" {} ''
        mkdir -p $out
        cp -r ${./public}/. $out/
      '';
      checksSource = pkgs.lib.fileset.toSource { root = ./.; fileset = pkgs.lib.fileset.unions [ ./public ./test ./scripts ]; };
      check = pkgs.runCommand "nickel-undo-model-check" { nativeBuildInputs = [ pkgs.nodejs_22 ]; } ''
        node ${checksSource}/scripts/portable.mjs --check
        node ${checksSource}/test/model.test.mjs
        node --check ${checksSource}/public/app.js
        touch $out
      '';
      server = pkgs.writeShellApplication {
        name = "nickel-undo-questionnaire";
        runtimeInputs = [ pkgs.darkhttpd ];
        text = ''exec darkhttpd ${site} --addr 127.0.0.1 --port "''${PORT:-4186}" --no-listing'';
      };
    in {
      packages.${system}.default = site;
      checks.${system}.default = check;
      apps.${system}.default = { type = "app"; program = "${server}/bin/nickel-undo-questionnaire"; meta.description = "Serve the static questionnaire on loopback"; };
      devShells.${system} = { default = pkgs.mkShell { packages = [ pkgs.nodejs_22 pkgs.darkhttpd ]; };
      browser = pkgs.mkShell {
        packages = [ pkgs.nodejs_22 pkgs.darkhttpd ];
        QUIZ_BROWSER_MODULE = "${pkgs.playwright-driver}/index.mjs";
        PLAYWRIGHT_BROWSERS_PATH = "${pkgs.playwright-driver.browsers}";
      }; };
    }) [ "x86_64-linux" "aarch64-linux" ]);
}
