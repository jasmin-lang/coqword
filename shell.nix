with import <nixpkgs> {};

let
  coqPackages = coqPackages_8_16;
  mathcomp = coqPackages.mathcomp;
in

stdenv.mkDerivation {
name = "coqword-0.0.0";

src = null;

buildInputs = [ ocaml dune_3 coqPackages.coq mathcomp.ssreflect mathcomp.fingroup mathcomp.algebra ];

}
