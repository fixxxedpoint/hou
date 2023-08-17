with (import <nixpkgs> { });

let
  sources = import ./nix/sources.nix {};
  pkgs = import sources.nixpkgs {};
in
with pkgs; mkShell {
  nativeBuildInputs = [
    perl
    gcc
    zlib
    haskell.compiler.ghc945
    haskellPackages.cabal-install
    # haskell.packages.ghc945.cabal-install
    haskell.packages.ghc945.haskell-language-server
    # haskell.packages.ghc945.apply-refact
    haskellPackages.apply-refact
    haskellPackages.hlint
    haskellPackages.stylish-haskell
    haskellPackages.hasktags
    haskellPackages.hoogle
    haskellPackages.hindent
  ];

  src = ./.;
}
