{ sources ? import ./nix/sources.nix {}
, pkgs ? import (fetchTarball { inherit (sources.nixpkgs) url sha256; }) {}
}:
pkgs.mkShell {
  buildInputs = [
    pkgs.nodejs
    pkgs.vscode
  ];
}
