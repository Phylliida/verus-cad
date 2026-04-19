{ pkgs ? import <nixpkgs> {}}:

pkgs.mkShell {
  packages = [
    pkgs.lean4
    pkgs.elan

  ];
}
