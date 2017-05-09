COQC=coqc
SRC=$(wildcard *v)

all: jscoq udoc $(SRC:%.v=%.html)

jscoq:
	git clone https://github.com/ejgallego/jscoq-builds.git --depth 1 -b v8.6 jscoq
	cd jscoq && git checkout 8a44193335dc935274393fd6abd6bf45f2062b9a

udoc: udoc.patch
	rm -rf udoc
	git clone https://github.com/ejgallego/udoc.git
	cd udoc && git checkout d30a1cabcd4b35a8e60104c7a3855bf4ca60398e
	-cd udoc && make # requires ocaml 4.02


%.html : %.v Makefile
	-$(COQC) $* # if not working, no links but html still ok
	./udoc/udoc.byte $< -o $@
	sed -i 's?^ *<title.*?<title>$*</title>?' $@
	sed -i 's?^ *<h1>$*</h1>??' $@
	sed -i '/<\/title>/a\<link rel="stylesheet" href="local.css" />' $@

run:
	python3 -m http.server 8000
