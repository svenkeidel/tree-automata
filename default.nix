{ mkDerivation, base, Cabal, containers, deepseq, mtl, parsec
, random, stdenv, syb
}:
mkDerivation {
  pname = "tree-automata";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base Cabal containers deepseq mtl parsec random syb
  ];
  homepage = "https://github.com/svenkeidel/tree-automata.git";
  description = "Regular tree automata";
  license = stdenv.lib.licenses.bsd3;
}
