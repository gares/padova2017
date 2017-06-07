
From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.
Open Scope list_scope.


(** #<div class='slide'># 
** Discriminazione dei costruttori e sotto tipi

   - definiamo il tipo dei numeri naturali positivi
   - usiamolo per programmare la funzione [pred]

*)

Definition positivo := { n : nat | ~ n = 0 }.
Locate "{ _ | _ }".
Print sig.

Lemma ex_falso P : False -> P.
Proof. move=> abs. case: abs. Qed.

Definition pred (x : positivo) : nat.
Proof.
case: x.
move=> n.
case: n.
  move=> abs.
  apply: ex_falso.
  apply: abs.
  apply: erefl.
move=> p _.
apply: p.
Defined.


(** Dobbiamo dimostrare che, per sempio, [~ 3 = 0],
    per applciare [pred] a "3"
*)

Lemma not_3_0 : ~ (3 = 0).
Proof.
move=> E.
change (match 3 with O => True | S _ => False end).
rewrite E.
apply: I.
Qed.

Definition n3p : positivo := exist _ 3 not_3_0.

Eval compute in pred n3p.

(** Adesso generalizziamo [not_3_0] a [not_Sx_0] perchè
    ci servirà dopo *)

(**
 #<div class="concepts">#
 Concetti:
 - [sig] rappresenta un sotto tipo
 - [eixists] (il costruttore di sig) è come [pair], raggruppa due termini
   e possiamo usarlo per scrivere programmi
 - [change tipo] per cambiare la forma del goal
   corrente con una convertibile
 - dimostrare che 2 costruttori sono diversi
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide vfill'>#  
** Lezione 3

 - Induzione
   - programmiamo il principio per nat
   - prove per induzione su nat
   - accumulatori e generalizzazione
   - prove per induzione su liste

 - Esercizi

#</div># *)

(** -------------------------------------------- *)

(** #<div class="slide">#

  ** Dimostriamo (hem programmiamo) il principio di induzione per [nat]

  Se le prove sono programmi, allora abitiamo questo tipo, senza troppo
  riflettere a cosa significhi.
*)

Fixpoint build_vector (vect : nat -> Type)
    (p0 : vect 0) (pS : forall n, vect n -> vect (S n)) (n : nat) : vect n
:=
  match n with
  | O => p0
  | S q => pS q (build_vector vect p0 pS q)
  end.

Check build_vector.

(** Abbiamo ottenuto il principio di induzione! 

    Beh, anche Coq lo sa fare... Infatti non appena uno
    definisce il tipo [nat] Coq genera questo programma
    in modo automatico:
*)

Check nat_rect.

(**
#<div class="concepts">#
 Concetti:
 - I principi di induzione non sono altro che funzioni
   ricorsive
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class="slide">#
 ** La prima prova per induzione

*)

Lemma addn0 n: n + 0 = n.
Proof.
elim: n.
  apply: erefl.
move=> p IHp.
rewrite /= IHp.
apply: erefl.
Qed.

Print Nat.mul.

Lemma muln0 n : n * 0 = 0.
Proof.
elim: n.
  by [].
move=> p IHp.
by rewrite /= IHp.
Qed.

Lemma addnS n m : n + S m = S (n + m).
Proof.
elim: n.
  by [].
move=> p IHp /=.
by rewrite IHp.
Qed.

Lemma addnC n m : n + m = m + n.
Proof.
elim: n.
  by rewrite addn0 /=.
move=> p IHp /=.
by rewrite IHp addnS.
Qed.

Lemma addnA a b c : a + (b + c) = a + b + c.
Admitted. (* Esercizio *)

(**
#<div class="concepts">#
 Concetti:
 - [elim: n] per iniziare l'induzione
 - [rewrite /=] per calcolare all'avanti
 - [... => nomi]
 - [... => /=]
 - [by ...] per terminare un comando di prova
 #</div>#

#</div># *)

(** -------------------------------------------- *)


(** #<div class="slide">#
 ** Accumulatori e generalizzazione

*)

Fixpoint append {A} l1 l2 : list A :=
  match l1 with
  | nil => l2
  | x :: xs => x :: append xs l2
  end.

Fixpoint rev {A} l : list A :=
  match l with
  | nil => nil
  | x :: xs => append (rev xs) (x :: nil)
  end.

Fixpoint fold {A B} (f : A -> B -> B) (l : list A) (b : B) : B :=
  match l with
  | nil => b
  | x :: xs => fold f xs (f x b)
  end.

Lemma fold_append1 x l acc :
  fold Nat.add (append l (x :: nil)) acc = fold Nat.add l (x + acc).
Proof.
elim: l acc => //= y ys IH acc.
by rewrite IH addnA [x + _]addnC addnA.
Qed.

Lemma fold_add l : fold Nat.add l 0 = fold Nat.add (rev l) 0.
Proof.
elim: l 0 => //= x xs IH acc.
by rewrite IH fold_append1.
Qed. 

(**
#<div class="concepts">#
 Concetti:
 - [=> //=] per semplificare e eliminare goal triviali
 - [elim: main gens] per generalizzare prima di fare l'induzione
 #</div>#

#</div># *)

(** ----------------------------------------- *)

(** #<div class="slide">#
 ** Indici e inversione

*)


Inductive is_leq (n : nat) : nat -> Type :=
  | leq_nn : is_leq n n
  | leq_S  : forall m, is_leq n m -> is_leq n (S m).

Infix "<=" := is_leq.

Lemma test_is_leq : 3 <= 5.
Proof.
apply: leq_S.
apply: leq_S.
apply: leq_nn.
Qed.

Lemma test_is_leq_hyp n m : S n <= m -> n <= m.
Proof.
move=> leq_Snm.
elim: leq_Snm.
  by apply: leq_S; apply: leq_nn.
by move=> a leq_Sna IH; apply: leq_S; apply: IH.
Qed.

Lemma is_leq0 n : n <= 0 -> n = 0.
Proof.
move=> leqn0.
move: (erefl 0).
by case: {-2}_ / leqn0.
Qed.

(*
Definition is_leq0bis n : n <= 0 -> n = 0 :=
  fun p : n <= 0 =>
    match p 
      in is_leq _ i
      return i = 0 -> n = i
    with
    | leq_nn => fun (e : n = 0) => erefl n
    | leq_S m q => fun (e : S m = 0) =>  (* q : n <= m *)
         match not_Sx_0 m e with end
    end
      (erefl 0).
*)

(**
#<div class="concepts">#
 Concetti:
 - [move: (term)] per generare una equazione
 - [case: {occs}_ / h] per scegliere le occorrenze degli indici
   di [h] da sostituire
 - [inversion H] genera l'equazione e fa il [case: ../..] al volo
 #</div>#

#</div># *)


(** *** Link utili:
    - #<a href="https://hal.inria.fr/inria-00258384">manuale</a># del linguaggio di prova
    - #<a href="http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/basic-cheatsheet.pdf">cheat-sheet</a>#
    - #<a href="https://math-comp.github.io/mcb/">Libro (draft) sulla formalizzazione in Coq</a>#
*)

(** ----------------------------------------------- *)

(** #<div class="slide">#
 ** Esercizi

*)

Lemma addnA1 a b c : a + (b + c) = a + b + c.
Proof.
(*D*)by elim: a => //= p ->.
Qed.

(** 
#
<button onclick="hide('sol1')">Soluzione</button>
<div id='sol1' class='solution'>
<pre>
by elim: a => //= p -> .
</pre>
</div>
#
Note: se si da il nome [->] a una ipotesi equazionale, allora
la si sostituisce al volo.

*)

Lemma appendA A (l1 l2 l3 : list A) :
  append l1 (append l2 l3) = append (append l1 l2) l3.
Proof.
(*D*)by elim: l1 => //= x xs ->.
Qed.

(** 
#
<button onclick="hide('sol2')">Soluzione</button>
<div id='sol2' class='solution'>
<pre>
by elim: l1 => //= x xs ->.
</pre>
</div>
#
*)

Lemma append_nil A (l : list A) : append l nil = l.
Proof.
(*D*)by elim: l => //= x xs ->.
Qed.

(** 
#
<button onclick="hide('sol3')">Soluzione</button>
<div id='sol3' class='solution'>
<pre>
by elim: l => //= x xs ->.
</pre>
</div>
#
*)

Lemma append_cons A (l : list A) x xs :
  append l (x :: xs) = append (append l (x :: nil)) xs.
Proof.
(*D*)by elim: l => //= y ys ->. 
Qed.

(** 
#
<button onclick="hide('sol3x')">Soluzione</button>
<div id='sol3x' class='solution'>
<pre>
by elim: l => //= y ys ->.
</pre>
</div>
#
*)


Lemma rev_append A (l1 l2 : list A) : 
  rev (append l1 l2) = append (rev l2) (rev l1).
Proof.
(*D*)elim: l1.
(*D*)  by rewrite /= append_nil.
(*D*)move=> x xs /= ->.
(*D*)by rewrite appendA.
Qed.

(** 
#
<button onclick="hide('sol4')">Soluzione</button>
<div id='sol4' class='solution'>
<pre>
elim: l1.
  by rewrite /= append_nil.
move=> x xs /= ->.
by rewrite appendA.
</pre>
</div>
#
*)

Lemma revI A (l : list A) : rev (rev l) = l.
Proof.
(*D*) elim: l => //= x xs IH.
(*D*) by rewrite rev_append /= IH.
Qed.

(** 
#
<button onclick="hide('sol5')">Soluzione</button>
<div id='sol5' class='solution'>
<pre>
elim: l => //= x xs IH .
by rewrite rev_append /= IH.
</pre>
</div>
#
*)

(** In questo esercizio, prima di iniziare la prova bisogna
    capire quale invariante serve dimostrare.  In partcolare
    l'accumulatore nil (da generalizzare come ben sapete) non
    compare a destra. E questo è il problema che dovere risolvere...
    E la soluzione è uno dei lemmi che avete dimostrato prima! *)

Lemma fold_rev A (l : list A) : fold cons l nil = rev l.
Proof.
(*D*)rewrite -(append_nil A (rev l)).
(*D*)elim: l nil => //= x xs IH acc.
(*D*)by rewrite IH append_cons.
Qed.

(** 
#
<button onclick="hide('sol5x')">Soluzione</button>
<div id='sol5x' class='solution'>
<pre>
rewrite -(append_nil A (rev l)).
elim: l nil => //= x xs IH acc.
by rewrite IH append_cons.
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
