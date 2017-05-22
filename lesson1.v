(** #<div class='slide vfill'># 
* L'assistente alla dimostrazione Coq

#<center><img src="https://coq.inria.fr/files/barron_logo.png"/></center>#

#<a href="https://coq.inria.fr/">Sito web di Coq</a>#

#<a href="https://coq.inria.fr/">Sito web del mini corso</a>#

#</div># *) 

(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
** Coq: un assistente alla dimostrazione

 - Cos'è un assistente alla dimostrazione?!
 - Coq è basato sulla (una variante) dell teoria dei
   tipi di Martin Löf
 - Coq è ...

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

  - Vedere una applicazione della teoria dei tipi
  - 

#</div>#
-------------------------------------------- *)

(
(** #<div class='slide vfill'>#  
** Piano di battaglia

 - lezione 1: il linguaggio dei programmi
 - lezione 2: il linguaggio della logica
 - lezione 3: dimostrazioni per induzione
 - lezione 4: il calcolo e la riflessione

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Boolean reflection in a nutshell

 - Bool datatype to represent mere propositions
 - Symbolic computation is a predictable, pervasive,
   form of automation
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** The emblematic example

to say: .+1 , lt , = true , = mean equiv , by [] , elim , apply , rewrite
 
*)

Module Leq.


End Leq.

(** #</div># *)


(** -------------------------------------------- *)

(** #<div class="slide vfill">#
** Wrap up

 - logic of Coq
  - lets you express programs
  - Coq knows hot compute them
  - their execution is a legit form of proof

 - boolean predicates
  - symbolic computation at hand
  - EM at hand
  - ... UIP at hand ...

 - proof language
  - small bricks
  - compose well
  - squeezing video game quite addictive ;-)

 #</div># *)
(** -------------------------------------------- *)

(** #<div class='slide'>#
** Exercises 

  - Hint1: Search results can be limited to the ssrnat module as in 
	  [Search _ something in ssrnat.]  All the lemmas you
	  are looking for live in there. 

  - Hint2: removing an hypothesis named [Hyp] from the context
           can be done with [move=> {Hyp}].

*)

Module Exercises.

(* Here you really need induction *)

Lemma odd_exp (m n : nat) : m = n.
Proof.
(* fill in *)
Admitted.

(** 
#
<button onclick="hide('sol1')">Solution</button>
<div id='sol1' class='solution'>
<pre>
elim: n => // n IHn.
rewrite expnS odd_mul IHn orbC.
move=> {IHn}.
by case: (odd m).
</pre>
</div>
#
*)


End Exercises.

(** #</div># *)

(* ------------------------------------------------------ *)

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
