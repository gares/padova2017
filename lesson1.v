(** #<div class='slide vfill'># 
* L'assistente alla dimostrazione Coq

#<center><img src="https://coq.inria.fr/files/barron_logo.png"/></center>#

#<a href="https://coq.inria.fr/">Sito web di Coq</a>#

#<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/">Sito web del mini corso</a>#
http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/

#</div># *) 

(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
** Coq: un assistente alla dimostrazione

 - Cos'è un assistente alla dimostrazione?!
 - Coq è basato sulla (una variante) dell teoria dei
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
** Piano di battaglia

 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson1.html">lezione 1</a>#: il linguaggio dei programmi
 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson2.html">lezione 2</a>#: il linguaggio della logica
 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson3.html">lezione 3</a>#: dimostrazioni per induzione
 - #<a href="http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/lesson4.html">lezione 4</a>#: il calcolo e la riflessione

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Lezione 1

 - Programmazione in Coq
   - funzioni anonime e non
   - calcolo
   - tipi di dato algebrici
   - pattern matching
   - ricorsione
   - tipi di dato polimorfi
   - ordine superiore

 - Esercizi

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Funzioni

- Nota: anche se nat, + e 1 sono concetti definibili
  in Coq, l'ambiente iniziale non è vuoto ma contiene
  alcuni declarazioni (come i numeri naturali) utili
  a fare esempi

$$$$ 
f = x \mapsto x + 1
$$$$
$$$$
f : \mathcal{N} \to \mathcal{N}
$$$$

*)

Check (fun (x : nat) => x + 1).

Definition f (x : nat) : nat :=
  x + 1.

Definition g (x : nat) (y : nat) : nat :=
  f x * y.

(**
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Calcolo

 - Prendiamo la funzione (il programma) f definito
   in precedenza
$$$$ 
f = x \mapsto x + 1 : \mathcal{N} \to \mathcal{N}
$$$$
<<
Definition f (x : nat) : nat :=
  x + 1 .
>>

 - Chiediamo a Coq di calcolare la forma canonica
   dei termini seguenti
*)

Eval compute in 3 + 1.

Eval compute in (fun x => x + 1) 3.

Eval compute in f 3.

Eval compute in g 3 4.

(**
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Tipi di dato algebrici

 - Facciamo finta che i numeri naturali
   che abbiamo usato finora non sia disponibili
   e definiamoli noi
*)

Module ProvaBoolNat.

Inductive Bool := True | False.

(** True e False si chiamano costruttori, e
    corrispondono alle regole $$$$Tipo-I_n$$$$
    nelle note del corso *)

Check True.

Inductive Nat := Zero | Succ (n : Nat).

Check Zero.
Check Succ.

Check (Succ Zero).

(** Nota: esistono varie sintassi alternative,
    per esempio
<<
Inductive Nat :=
   Zero : Nat
 | Succ : Nat -> Nat.
>>

  Quella che abbiamo utilizzata è la più simile a quella
  usata nelle note del corso e anche nei linguaggi di
  programmazione.  Se chiediamo a Coq di stampare una
  dichiarazione di tipo con:

*)

Print Nat.

End ProvaBoolNat.

(** utilizzerà l'altra sintassi...

    Ora torniamo a utilizzare _nat_ (in minuscolo)
    e i suoi costruttori _S_ e _O_ (lettera O maiuscola)
    in quanto il sistema li stampa meglio (notazione decimale).
*)

Print nat.
Check (S O).
Set Printing All.
Check (S O).
Unset Printing All.
Check (S O).

(**
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Pattern matching

 - In Coq l'eliminatore (chiamato _El_ nelle note
   del corso) è fornito in _kit_:
   - il costrutto _match_ fornisce l'analisi per casi
   - il costrutto _Fixpoint_ (in seguito) fornisce
     l'ipotesi induttiva

*)

Definition notb (b : bool) :=
  match b with
  | true => false
  | false => true
  end.

Eval compute in notb true.
Eval compute in notb false. 

Definition andb (b1 : bool) (b2 : bool) :=
  match b1 with
  | true => b2
  | false => false
  end.

Eval compute in andb true true.
Eval compute in andb true false.

Definition predecessore (n : nat) : nat :=
  match n with
  | O => O
  | S p => p
  end.

(** 
  Note:
  - Ogni clausola del pattern matching è della forma
    << | pattern => corpo >>
    dove pattern è un costruttore applicato a un numero
    di variabili appropriato
  - Tutti i costruttori del tipo di dato devono essere
    trattati da un pattern
  - _p_ è una variabile legata dal pattern matching
    e può essere utilizzata nel corpo della clausola
  
  Esempio di esecuzione:
 <<
   match S (S O) with
   | O => O
   | S p => p
   end

   O    ==?== S (S O)  no, proviamo la prossima clausola
   S p  ==?== S (S O)  sì, p lega (S O)
 >>
*)

(**
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Ricorsione
*)

Fixpoint addn (n : nat) (m : nat) : nat :=
  match n with
  | O => m  (* 0 + m = m *)
  | S p => S (addn p m)   (* S p + m = S (p + m) *)
  end.

Eval compute in addn 2 4.

(** Esempio di esecuzione:
<<
  addn 2 4
  addn (S (S O)) 4
  S (addn (S O) 4)
  S (S (addn O 4))
  S (S 4)
  6
>>

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Tipi di dato polimorfi

 - La coppia (a,b) dove a : A e b : B
 - La list x1 :: .. :: xn dove x_i : A

*)

Inductive prod (A : Type) (B : Type) :=
  | pair (a : A) (b : B).

Check prod.
Check prod nat bool.
Check pair.

(** Nota: forall A B : Type, ci indica che il tipo
    pair è polimorfo, ovvero A e B possono essere rimpiazzati per
    un tipo di data *)

Check pair nat bool.
Check pair nat bool 3 false.

(** Nota: come assegnare il tipo a una applicazione
<<
      addn : nat -> nat -> nat
      addn 3 : nat -> nat
      addn 3 4 : nat
>>
    Se il tipo è quantificato, allora il valore
    dell'argomento sostituisce la variabile in ciò
    che rimane
<<
      pair : forall A, forall B, A -> B -> prod A B
      pair nat : forall B, nat -> B -> prod nat B
      pair nat bool : nat -> bool -> prod nat bool
      pair nat bool 3 : bool -> prod nat bool
      pair nat bool 3 false : prod nat bool
>>
*)

Definition fst (A : Type) (B : Type) (x : prod A B) : A :=
  match x with
  | pair _ _ x1 x2 => x1
  end.

Eval compute in fst nat bool (pair nat bool 3 false).

(** Argomenti impliciti (inferiti da Coq) *)

Check pair _ _ 3 false.
Eval compute in fst _ _ (pair _ _ 3 false).

Arguments pair {_ _} a b.
Arguments fst {_ _} x.

Check pair 3 false.
Eval compute in fst (pair 3 false).

Definition snd (A : Type) (B : Type) (x : prod A B) : B :=
  match x with
  | pair x1 x2 => x2
  end.

(** #</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Liste

*)

Inductive list (A : Type) :=
  nil | cons (a : A) (tl : list A).

Arguments nil {_}.
Arguments cons {_} a tl.

Fixpoint length A (l : list A) : nat :=
  match l with
  | nil => 0
  | cons x xs => S (length A xs)
  end.

Arguments length {_} l.

Eval compute in length (cons 3 (cons 4 nil)).

(** #</div># *)

(** -------------------------------------------- *)

(** #<div class="slide vfill">#
** Wrap up

 - ....

 #</div># *)
(** -------------------------------------------- *)

(** #<div class='slide'>#
** Esercizi 


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
