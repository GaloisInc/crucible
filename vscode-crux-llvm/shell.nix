{ sources ? import ./nix/sources.nix { }
, pkgs ? import sources.nixpkgs { }
}:
pkgs.mkShell {

  buildInputs = [
    pkgs.nodejs
  ];

  name = "vscode-crux-llvm";

  # If you use lorri, add:
  # eval "${shellHook}"
  # to your .envrc
  shellHook = ''
    mkdir -p bin
    ln -fs ${pkgs.clang}/bin/clang bin/clang
    ln -fs ${pkgs.llvm}/bin/llvm-link bin/llvm-link
    ln -fs ${pkgs.z3}/bin/z3 bin/z3
  '';

}
