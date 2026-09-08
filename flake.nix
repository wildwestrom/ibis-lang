{
  description = "Ibis Lang Flake";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        legacyPackages = pkgs;
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            ghc
            cabal-install
          ];
        };
      }
    );
}
