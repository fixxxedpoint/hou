with (import <nixpkgs> { });

haskell.lib.buildStackProject {
  nativeBuildInputs = [
    perl
    gcc
  ];

  name = "hou";
  src = ./.;
}
