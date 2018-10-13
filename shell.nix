{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, containers, deepseq, hashable, hspec
      , HUnit, mtl, stdenv, text
      }:
      mkDerivation {
        pname = "tree-automata";
        version = "0.1.0.0";
        src = ./.;
        libraryHaskellDepends = [
          base containers deepseq hashable mtl text
        ];
        testHaskellDepends = [ base containers hspec HUnit mtl text ];
        homepage = "https://github.com/svenkeidel/tree-automata.git";
        description = "Regular tree automata";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
