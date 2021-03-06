SRC=$(wildcard *v)

all: jscoq udoc coq/bin/coqide $(SRC:%.v=%.html)

jscoq:
	git clone https://github.com/ejgallego/jscoq-builds.git --depth 1 -b v8.6 jscoq
	cd jscoq && git checkout 8a44193335dc935274393fd6abd6bf45f2062b9a

udoc/udoc.byte:
	-git clone https://github.com/ejgallego/udoc.git
	cd udoc && git checkout d30a1cabcd4b35a8e60104c7a3855bf4ca60398e
	-cd udoc && make # requires ocaml 4.02

coq/bin/coqide:
	-git clone https://github.com/coq/coq.git
	cd coq && git checkout v8.6 && ./configure -local && make -j2 coqide


%.html : %.v Makefile
	./coq/bin/coqc $*
	bash -c "./udoc/udoc.byte <( sed 's/^(\*D\*).*/(* completa... *)/' $< ) -o $@"
	sed -i "s#^ *<title.*#<title>$*</title><script type='text/javascript' src='https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-MML-AM_CHTML'> </script> <script type='text/javascript'> MathJax.Hub.Config({ 'HTML-CSS': { preferredFont: 'STIX' }, tex2jax: { inlineMath: [['XXX','XXX']] } }); </script>#" $@
	#sed -i "s#^ *<title.*#<title>$*</title><script type='text/javascript' src='MathJax-2.7.1/unpacked/MathJax.js?config=TeX-MML-AM_CHTML'> </script> <script type='text/javascript'> MathJax.Hub.Config({ 'HTML-CSS': { preferredFont: 'STIX' }, tex2jax: { inlineMath: [['XXX','XXX']] } }); </script>#" $@
	sed -i 's?^ *<h1>$*</h1>??' $@
	sed -i '/<\/title>/a\<link rel="stylesheet" href="local.css" />' $@

edit:
	./coq/bin/coqide lesson*v

deploy: jscoq

run-local:
	python3 -m http.server 8000


