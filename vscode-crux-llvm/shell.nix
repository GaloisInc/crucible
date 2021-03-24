{ sources ? import ./nix/sources.nix {}
, pkgs ? import (fetchTarball { inherit (sources.nixpkgs) url sha256; }) {}
}:
pkgs.mkShell {

  buildInputs = [
    pkgs.nodejs
    pkgs.vscode
  ];

  # If you use lorri, add:
  # eval "${shellHook}"
  # to your .envrc
  shellHook = ''
    ln -fs ${pkgs.clang}/bin/clang clang
    ln -fs ${pkgs.llvm}/bin/llvm-link llvm-link
    ln -fs ${pkgs.z3}/bin/z3 z3
  '';

}
