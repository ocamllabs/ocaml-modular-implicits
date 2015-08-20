case $XARCH in
i386)
  ./configure
  make world.opt
  sudo make install
  cd testsuite && make all

  git clone git://github.com/ocamllabs/camlp4
  (cd camlp4                              \
   && git checkout modular-implicits-4.02 \
   && ./configure                         \
   && make)
  ;;
*)
  echo unknown arch
  exit 1
  ;;
esac
