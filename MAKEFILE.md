targets:
- all (default): compile Lambdapi
- doc: generate in lambdapi.docdir/ HTML files describing the types and functions exported by Lambdapi
- install: install Lambdapi
- install_vim: install Vim mode for Lambdapi
- uninstall: uninstall Lambdapi
- clean: remove files generated by OCaml
- distclean: remove files generated by OCaml and Lambdapi
- fullclean: remove files generated by OCaml and Lambdapi, and downloaded library files
- tests: run basic tests without failing
- real_tests: run basic tests, stoping at the first failure
- dklib: run Lambdapi on https://github.com/rafoo/dklib/
- plein_de_dks: run Lambdapi on https://git.lsv.fr/genestier/PleinDeDk/
- focalide: run Lambdapi on the Dedukti files generated from the Focalize library
- holide: run Lambdapi on the Dedukti files generated from the OpenTheory library
- matita: run Lambdapi on the Dedukti files generated from the arithmetic library of Matita
- verine: run Lambdapi on some Dedukti files generated by VeriT
- iprover: run Lambdapi on some Dedukti files generated by iProverModulo
- zenon_modulo: run Lambdapi on some Dedukti files generated by ZenonModulo
