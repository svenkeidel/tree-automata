{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, Cabal, containers, deepseq, mtl, parsec
      , random, stdenv, syb, cabal-install
      }:
      mkDerivation {
        pname = "tree-automata";
        version = "0.1.0.0";
        src = ./.;
        libraryHaskellDepends = [
          base Cabal containers deepseq mtl parsec random syb cabal-install
        ];
        homepage = "https://github.com/svenkeidel/tree-automata.git";
        description = "Regular tree automata";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
