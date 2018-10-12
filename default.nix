{ mkDerivation, base, Cabal, containers, deepseq, mtl, parsec
, random, stdenv, syb, hspec, hashable
}:
mkDerivation {
  pname = "tree-automata";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base Cabal containers deepseq mtl parsec random syb hspec hashable
  ];
  homepage = "https://github.com/svenkeidel/tree-automata.git";
  description = "Regular tree automata";
  license = stdenv.lib.licenses.bsd3;
}
