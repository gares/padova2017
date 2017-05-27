(**

* L'assistente alla dimostrazione Coq

#<center><img src="https://coq.inria.fr/files/barron_logo.png"/></center>#

#<a href="https://coq.inria.fr/">Sito web di Coq</a>#

#<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/">Sito web del mini corso</a>#
http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/

** Lezioni

 - 1 Coq: un linguaggio di programmazione funzionale (31/5/2017)
 - 2 Curry Howard: la logica di Coq e le prime dimostrazioni (1/6/2017)
 - 3 Induzione: proprietà di programmi ricorsivi (7/6/2017)
 - 4 Riflessione computazionale: l'esecusione di un programma è una prova (8/6/2017)

** Pagina di prova

 Coq può funzionare dentro il browser (navigatore).

 - attendi che la pagina si carichi, un pannello si apre sulla destra
 - verifica con Coq ogni linea del documento premendo ALT-N (le frasi
   accettate da Coq diventano grigio chiaro).
 - torna indietro con ALT-P
 - OK, tutto funziona!

*) 

Lemma test : 2 + 1 = 3.
Proof.
trivial.
Qed.