(** #<div class='slide vfill'>#  
** Lezione 4

 - Applicazioni di Coq
   - un compilatore C verificato
   - un libreria di matematica organizzata
     come una libreria di programmi 

 - Riflessione computazionale
   - idea
   - normalizzazione nella segnatura di
     un monoide

 - Esercizio

#</div># *)

From mathcomp Require Import all_ssreflect.


(** ----------------------------------- *)

(** #<div class='slide'># 
** Applicazione: Compilatore certificato CompCert 

   CompCert è un vero e proprio compilatore C.
   Il compilatore è scritto in OCaml.
   Il codice OCaml è extratto da programmi/prove Coq.

   #<a href="http://compcert.inria.fr/">Sito del compilatore</a>#

   Tecniche:
   - estrazione di programmi da termini Coq
   - verifica correttezza traccia esterna per riflessione computazionale

*)

Definition positivo := { n : nat | ~ n = 0 }.
Locate "{ _ | _ }".
Print sig.

Definition pred (x : positivo) : nat :=
match x with
| exist n p =>
    match n with
    | O => fun abs : ~ O = O =>
               match abs (erefl 0) with end
    | S x => fun _ => x
    end 
      (p : ~ n = 0)
end.

Lemma not_3_0 : ~ (3 = 0).
Proof.
move=> E.
change (match 3 with O => True | S _ => False end).
rewrite E.
apply: I.
Qed.

Definition n3p : positivo := exist _ 3 not_3_0.

Definition e := pred n3p.

(* Extraction Language Haskell. *)
Recursive Extraction e.

(** Ora proviamo il programma estratto in
    #<a href="https://try.ocamlpro.com/">OCaml</a># *)

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Applicazione: Verfica di prove di matematica 

   La libreria #<a href="http://math-comp.github.io/math-comp/">Mathematical Components</a>#
   e il #<a href="https://math-comp.github.io/mcb/">Libro (draft)</a># sulla formalizzazione in Coq
   di tale libreria.

   Tecniche utilizzate:
   - riflessione booleana (predicati decidibili = programmi)
   - programmazione logica (inferenza di tipo à la type-classes)

*)

From mathcomp Require Import all_ssreflect.

Lemma test_tuple A n (t : n.-tuple A):
  size t = size (rev (map id t)).
Proof.
rewrite size_tuple.
(*
Check (erefl _ : size (rev (map id (tval t))) = size (tval _)).
Check rev_tuple.
Print rev_tuple.
Check rev_tupleP.
*)
rewrite size_tuple.
by [].
Qed.

From mathcomp Require Import all_fingroup.
Open Scope group_scope.


Lemma test (gT : finGroupType) (G H : {group gT}) : 1 \in G :&: H.
Proof.
Check (G :&: H).
About group1.
Check (erefl _ :  (G :&: H) = gval _).
About setI_group.
Print setI_group.
About group_setI.
change (1 \in gval (setI_group G H)).
apply: group1.
Qed.

Close Scope group_scope.
Open Scope nat_scope.

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** 
   Bello:
   - nella teoria dei tipi dimostrare [2+3=3+2] è facile,
     o meglio, la dimostrazione è _molto_ corta [apply: erefl]
   - tale dimostrazione non dipende dalla taglia delle espressioni
     coinvolte, ie rimane triviale anche per [2+3+4+5=5+2+3+4]
   Meno bello:
   - il calcollo è completo su termini chiusi, se sono presenti
     variabili dobbiamo ragionare per induzione o riutilizzare lemmi
     dimostrati in precendenza, eg [x + 0 = x]
   - la taglia della dimostrazione dipende però dal numero di passi
     da fare, eg [(x + 0) + 0 = x] richiede 2 riscritture

   Osservazione:
   - l'esecuzione di un programma [p] non richiede una prova
     [p x = y]
   - e non importa quanti "passi" di esecuzione [p] faccia
     la prova di [p x = y] è sempre [erefl]

   Idea: potremmo scrivere un programma che "fa la dimostrazione"
   (quando questa è ripetitiva).

   Per empio [p] potrebbe prendere una expressione in
   un monoide e metterla in forma normale, e.g.
 
     x + 0 + (y + 0) ----> x + y

   Iniziamo col dare una rappresentazione concreta (un dato
   induttivo) alle espressioni nel monoide.
*)

(** #</div># *)

Inductive Syntax A :=
  | Identity
  | Value (a : A)
  | Op (m1 : Syntax A) (m2 : Syntax A).

Arguments Identity {_}.
Arguments Value {_} a.
Arguments Op {_} m1 m2. 

(* 3 + (0 + 2) *)
Definition example : Syntax nat := 
  (Op (Value 3) (Op Identity (Value 2))).

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Intepretazione

  Il termine [x + (0 + y)] è di tipo [nat] ed è
  un termine che potremmo trovare in un goal.
  La sua rappresentazione sintattica [Op (Value x) ..]
  non ha tipo [nat], anche se rappresenta un termine
  di tale tipo.

  Scriviamo una funziona che interpreta una
  espressione sintattica in un monoide

 *)


Fixpoint interp {A} op id (m : Syntax A) :=
  match m with
  | Identity => id
  | Value x => x
  | Op l r => op (interp op id l) (interp op id r)
  end.


Eval compute -[addn] in interp addn 0 example.
Eval compute -[muln] in interp muln 1 example.

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Normalizzazione 

     Op Identity x --> x
     Op x Identity --> x
     Op x (Op y z) --> Op (Op x y) z

*)

Fixpoint norm {A} (m : Syntax A) :=
  match m with
  | Identity => Identity
  | Value x => Value x
  | Op l r =>
      let l := norm l in
      let r := norm r in
      match l, r with
      | Identity, _ => r
      | _, Identity => l
      | _, Op a b => Op (Op l a) b
      | _, _ => Op l r
      end
   end.

Eval compute -[addn] in interp addn 0 (norm example).

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Correttezza dell'algoritmo di normalizzazione *)

Lemma norm_ok {A op id} :
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op id a = a) ->
  (forall a, op a id = a) ->
  forall (m : Syntax A), 
    interp op id m = interp op id (norm m).
Proof.
move=> opA idL idR m.
elim: m => //= e1 -> e2 ->.
by case: (norm e1); case: (norm e2) => /=.
Qed.

Lemma test2 x y :
  x + (y + 0) + 0 = x + y.
Proof.
rewrite /=.
pose s := Op (Op (Value x) (Op (Value y) Identity)) Identity.
change (interp addn 0 s = x+y).
rewrite (norm_ok addnA add0n addn0).
rewrite /=.
apply: erefl.
Qed.

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Reificazione 

  Non è una funzione delle teoria dei tipi:
  - la teoria quozienta i termini wrt il calcolo
  - [1 + 1] e [2] sono indistinguibili
  - ma [Op (Value 1) (Value 1)] e [Value 2] sono
    ben diversi!
  - quello che è preservato è il significato (interpretazione)
  
  Soluzione: la funzione di reificazione la scriviamo un
  linguaggio che non è la teoria dei tipi ;-)

  Fortuna: non ci interessa dimostrarla corretta, basta
  che lo sia in pratica.

*)

Ltac quote op id t :=
  match t with
  | (op ?a ?b) =>
        let x := quote op id a in
        let y := quote op id b in
        uconstr:(Op x y)
  | id => uconstr:(Identity)
  | ?x => uconstr:(Value x)
  end.

Ltac monoid op id opA idL idR :=
  match goal with
  |- ?a = ?b =>
      let x := quote op id a in
      let y := quote op id b in 
      change (interp op id x = interp op id y);
      rewrite [interp op id x](norm_ok opA idL idR);
      rewrite [interp op id y](norm_ok opA idL idR);
      compute -[op]
  end.

Lemma test3 x y :
  x + (y + 0) + 0 = 0 + x + y. 
Proof.
monoid addn 0 addnA add0n addn0.
apply: erefl.
Qed.

Lemma test4 x y :
  x * (y * 1) = x * y. 
Proof.
monoid muln 1 mulnA mul1n muln1.
apply: erefl.
Qed.

(** #</div># *)

(** #<div class='slide'># 
** Esercizio: 

   aggiungere un elemento assorbente
   al monoide (sintassi, interpretazione, normalizzazione,
   prova di correttezza, codice [quote] e codice [monoid]) 
*)


Lemma esercizio x y :
  x * (y * 1) * 0 = x * 0. 
Proof.
(* questa prova deve funzionare:
monoid muln 1 0 mulnA mul1n muln1 mul0n muln0.
apply: erefl.
Qed.
*)
Admitted.

(** 
#
<button onclick="hide('sol11')">Soluzione</button>
<div id='sol11' class='solution'>
<pre>


Inductive Syntax A :=
  | Identity
  | Annihilator
  | Value (a : A)
  | Op (m1 : Syntax A) (m2 : Syntax A).

Arguments Value {_} a.
Arguments Op {_} m1 m2.
Arguments Identity {_}.
Arguments Annihilator {_}.

Fixpoint interp {A} op id abs (m : Syntax A) :=
  match m with
  | Identity => id
  | Annihilator => abs
  | Value x => x
  | Op l r => op (interp op id abs l) (interp op id abs r)
  end.

Fixpoint norm {A} (m : Syntax A) :=
  match m with
  | Identity => Identity
  | Annihilator => Annihilator
  | Value x => Value x
  | Op l r =>
      let l := norm l in
      let r := norm r in
      match l, r with
      | Annihilator, _ => Annihilator
      | _, Annihilator => Annihilator
      | Identity, _ => r
      | _, Identity => l
      | _, Op a b => Op (Op l a) b
      | _, _ => Op l r
      end
   end.

Lemma norm_ok {A op id abs} :
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op id a = a) ->
  (forall a, op a id = a) ->
  (forall a, op abs a = abs) ->
  (forall a, op a abs = abs) ->
  forall (m : Syntax A), 
    interp op id abs m = interp op id abs (norm m).
Proof.
move=> opA idL idR abdL absR m.
elim: m => //= e1 -> e2 ->.
case: (norm e1); case: (norm e2) => //=.
Qed.

Ltac quote op id abs t :=
  match t with
  | (op ?a ?b) =>
        let x := quote op id abs a in
        let y := quote op id abs b in
        uconstr:(Op x y)
  | id => uconstr:(Identity)
  | abs => uconstr:(Annihilator)
  | ?x => uconstr:(Value x)
  end.

Ltac monoid op id abs opA idL idR absL absR :=
  match goal with
  |- ?a = ?b =>
      let x := quote op id abs a in
      let y := quote op id abs b in 
      change (interp op id abs x = interp op id abs y);
      rewrite [interp op id abs x](norm_ok opA idL idR absL absR);
      rewrite [interp op id abs y](norm_ok opA idL idR absL absR);
      compute -[op]
  end.

</pre>
</div>
#
*)


(** #</div># *)

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
