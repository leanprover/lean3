let pkgs = import <nixpkgs> {}; in
{ stdenv ? pkgs.stdenv
, cmake ? pkgs.cmake
, gmp ? pkgs.gmp
, mpfr ? pkgs.mpfr
, boost ? pkgs.boost
, python ? pkgs.python
, gperftools ? pkgs.gperftools
, ninja ? pkgs.ninja
}:

stdenv.mkDerivation rec {
  name = "lean";

  src = builtins.filterSource (path: type: baseNameOf path != ".git") ./.;

  buildInputs = [ gmp mpfr boost cmake python gperftools ninja ];

  enableParallelBuilding = true;

  postUnpack = "sourceRoot=lean/src";

  cmakeFlags = [ "-DCMAKE_BUILD_TYPE=Release" "-DNINJA_PATH=${ninja}/bin/ninja" ];

  meta = with stdenv.lib; {
    description = "Automatic and interactive theorem prover";
    homepage    = "http://leanprover.github.io";
    license     = licenses.asl20;
    platforms   = platforms.unix;
  };
}
