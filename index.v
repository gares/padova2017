(** #<div class='slide >#

* L'assistente alla dimostrazione Coq

#<center><img src="https://coq.inria.fr/files/barron_logo.png"/></center>#

#<a href="https://coq.inria.fr/">Sito web di Coq</a>#

#<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/">Sito web del mini corso</a>#
http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/

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

(** #</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
* Introduzione

** Coq: un assistente alla dimostrazione

 - Cos'è un assistente alla dimostrazione?!
 - Coq è basato sulla (una variante) della teoria dei
   tipi di Martin Löf
 - Coq è utilizzato per
   - formalizzare matematica
   - verificare software

#</div># *) 

(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
** Chi sono io?

 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/">Enrico Tassi</a>#
 - Sviluppatore Coq
 - Ricercatore (implementazione PA e loro utilizzo)

#</div># *) 

(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
** Obiettivi del mini corso

  - Vedere una applicazione pratica della teoria dei tipi
  - Introduzione a un assistente alla dimostrazione
    (proof assistant, interactive theorem prover)

#</div>#
-------------------------------------------- *)

(** #<div class='slide vfill'># 
** Lezioni

 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson1.html">lezione 1</a>#: Coq: un linguaggio di programmazione funzionale
 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson2.html">lezione 2</a>#: Curry Howard: la logica di Coq e le prime dimostrazioni
 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson3.html">lezione 3</a>#: Induzione: proprietà di programmi ricorsivi
 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson4.html">lezione 4</a>#: Riflessione computazionale: l'esecuzione di un programma è una prova

#</div>#
-------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Iniziamo!

 #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson1.html">Prima lezione</a>#:
   Coq: un linguaggio di programmazione funzionale

#</div># *)

(**
#
<script>
alignWithTop = true;
current = 0;
slides = [];
function select_current() {
  for (var i = 0; i < slides.length; i++) {
    var s = document.getElementById('slideno' + i);
    if (i == current) {
      s.setAttribute('class','slideno selected');
    } else {
      s.setAttribute('class','slideno');
    }
  }	
}
function init_slides() {
  var toolbar = document.getElementById('panel-wrapper');
  if (toolbar) {
  var tools = document.createElement("div");
  var tprev = document.createElement("div");
  var tnext = document.createElement("div");
  tools.setAttribute('id','tools');
  tprev.setAttribute('id','prev');
  tprev.setAttribute('onclick','prev_slide();');
  tnext.setAttribute('id','next');
  tnext.setAttribute('onclick','next_slide();');
  toolbar.appendChild(tools);
  tools.appendChild(tprev);
  tools.appendChild(tnext);
  
  slides = document.getElementsByClassName('slide');
  for (var i = 0; i < slides.length; i++) {
    var s = document.createElement("div");
    s.setAttribute('id','slideno' + i);
    s.setAttribute('class','slideno');
    s.setAttribute('onclick','goto_slide('+ i +');');
    s.innerHTML = i;
    tools.appendChild(s);
  }
  select_current();
  } else {
  //retry later
  setTimeout(init_slides,100);	  
  }
}
function on_screen(rect) {
  return (
    rect.top >= 0 &&
    rect.top <= (window.innerHeight || document.documentElement.clientHeight)
  );
}
function update_scrolled(){
  for (var i = slides.length-1; i >= 0; i--) {
    var rect = slides[i].getBoundingClientRect();
      if (on_screen(rect)) {
        current = i;
        select_current();	
    }
  }
}
function goto_slide(n) {
  current = n;
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function next_slide() {
  current++;
  if (current >= slides.length) { current = slides.length - 1; }
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function prev_slide() {
  current--;
  if (current < 0) { current = 0; }
  var element = slides[current];
  element.scrollIntoView(alignWithTop);
  select_current();
}
function hide (element_id) {
  element = document.getElementById(element_id);
    if (element.style.display != 'block') {
      element.style.display = 'block';
    } else {
      element.style.display = 'none';
    }
}
window.onload = init_slides;
window.onscroll = update_scrolled;
</script>
# *)
