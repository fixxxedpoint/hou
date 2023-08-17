with (import <nixpkgs> { });

let
  sources = import ./nix/sources.nix {};
  pkgs = import sources.nixpkgs {};
in
with pkgs; mkShell {
  nativeBuildInputs = [
    perl
    gcc
    haskell.compiler.ghc945
    haskellPackages.cabal-install
    haskell.packages.ghc945.haskell-language-server
    haskellPackages.apply-refact
    haskellPackages.hlint
    haskellPackages.stylish-haskell
    haskellPackages.hasktags
    haskellPackages.hoogle
    haskellPackages.hindent
    haskellPackages.hspec
  ];
  
  buildInputs = [ zlib ];
}
