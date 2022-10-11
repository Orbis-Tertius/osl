{
  nixConfig.bash-prompt = "[nix-develop-osl:] ";
  description = "Orbis Specification Language compiler";
  inputs = {
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
    flake-compat-ci.url = "github:hercules-ci/flake-compat-ci";
    lint-utils = {
      url = "git+https://gitlab.homotopic.tech/nix/lint-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    safe-coloured-text-src = {
      url = "github:NorfairKing/safe-coloured-text/675cb01fce5f46718416d7746de5b856ed90a63f";
      flake = false;
    };
    autodocodec-src = {
      url = "github:NorfairKing/autodocodec/c8c6965d97a04fb483c03c0a8479533f252a34d7";
      flake = false;
    };
  };
  outputs =
    inputs@
    { self
    , flake-utils
    , flake-compat-ci
    , lint-utils
    , nixpkgs
    , safe-coloured-text-src
    , autodocodec-src
    , ...
    }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
    let
      pkgs = import nixpkgs { inherit system; };
      lintPkgs = import lint-utils.inputs.nixpkgs { inherit system; };
      hsPkgs =
        with pkgs.haskell.lib;
        pkgs.haskell.packages.ghc924.override
          {
            overrides = hfinal: hprev:
              {
                safe-coloured-text = hprev.callCabal2nix "safe-coloured-text" (safe-coloured-text-src + /safe-coloured-text) { };
                autodocodec-yaml = hprev.callCabal2nix "autodocodec" (autodocodec-src + /autodocodec-yaml) { };
                osl = disableLibraryProfiling (hprev.callCabal2nix "osl" ./. { });
                osl-spec = disableLibraryProfiling (hprev.callCabal2nix "osl:spec" ./. { });
              };
          };
      ormolu-check =
        pkgs.stdenv.mkDerivation {
          name = "ormolu-check";
          src = ./.;
          doCheck = true;
          buildPhase = ''
            ${pkgs.git.outPath}/bin/git init
            ${pkgs.git.outPath}/bin/git add -A
            ${pkgs.git.outPath}/bin/git config user.email "foo@bar.com"
            ${pkgs.git.outPath}/bin/git config user.name "Foobar"
            ${pkgs.git.outPath}/bin/git commit -m "initial commit"
            ${hsPkgs.ormolu.outPath}/bin/ormolu -m inplace $(find ./. -type f -name '*.hs')
            if [ -z "$(${pkgs.git.outPath}/bin/git status --porcelain)" ]; then
              echo "ok"
            else
              echo "ormolu check failed"
              exit 1
            fi
          '';
          installPhase = ''
            mkdir -p $out
          '';
        };
    in
    {
      devShells.default = hsPkgs.osl.env.overrideAttrs (attrs: {
        buildInputs = attrs.buildInputs ++ [
          hsPkgs.cabal-install
          pkgs.nixpkgs-fmt
          hsPkgs.ghcid
          hsPkgs.ormolu
          hsPkgs.hlint
        ];
      });
      packages.default = hsPkgs.osl;
      packages.ormolu-check = ormolu-check;
      ciNix = flake-compat-ci.lib.recurseIntoFlakeWith {
        flake = self;
        systems = [ "x86_64-linux" ];
      };
      checks =
        with lint-utils.outputs.linters.${system};
        {
          hlint = hlint self;
          hpack = hpack self;
          nixpkgs-fmt = nixpkgs-fmt self;
          inherit ormolu-check;
          spec = hsPkgs.osl-spec;
        };
    });

}
