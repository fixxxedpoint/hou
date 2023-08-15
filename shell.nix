with (import <nixpkgs> {});

let
  project = import ./default.nix;
  nativeBuildInputs = project.nativeBuildInputs ++ [
    haskellPackages.apply-refact
    haskellPackages.hlint
    haskellPackages.stylish-haskell
    haskellPackages.hasktags
    haskellPackages.hoogle
    haskellPackages.haskell-language-server
  ];
in
mkShell {
  inherit nativeBuildInputs;
  inherit (project) buildInputs;
}

