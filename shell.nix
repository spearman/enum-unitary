with import <nixpkgs> {};
pkgs.mkShell {
  buildInputs = [ rustup rust-analyzer ];
}
