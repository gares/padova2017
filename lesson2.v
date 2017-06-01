(** Note sulla lezione 1

- [match .. with .. end] è un termine e può
  essere usato dovunque, non solo alla radice
*)

Fixpoint odd  n :=
  match n with
  | O => false
  | S p =>
     match p with
     | O => true
     | S q => odd q
     end
  end.

Definition notb b := match b with true => false | false => true end.

Fixpoint odd2  n :=
  match n with
  | O => false
  | S p => notb (odd2 p)
  end.
(**

  E le chiamae ricorsive sono accettate anche su
  sotto-sotto-termini

- I tipi induttivi ammetteno un principio di induzione/
  ricorsione standard
*)

Check nat_rect.
Check (nat_rect (fun x => bool)).

Definition odd3 :=
  nat_rect (fun x => bool)
    false
    (fun p b => notb b).
Eval compute in odd3 4.
Eval compute -[notb] in odd3.

(** Tipi di dato indiciati e i
    casi impossibili *)
Module Vector.

  Inductive vect (A : Type) : nat -> Type :=
  | vnil : vect A 0
  | vcons : forall n, A -> vect A n -> vect A (1+n).

  Arguments vnil {_}.
  Arguments vcons {_ _} _ _.

  Definition hd {A n} (v : vect A (S n)) : A :=
  match v in vect _ l return
    match l with
    | S _ => A
    | O => bool
    end
  with
  | vcons x xs => x
  | vnil => true
  end.

  Fail Check hd (vnil nat).
  Eval compute in
    hd (vcons 3 (vcons 2 vnil)).
  Check  (vcons 3 (vcons 2 vnil)).

End Vector.

(** ----------------------------- *)

(** #<div class='slide vfill'>#  
** Lezione 2

 - Curry Howard: la logica di Coq e le prime dimostrazioni
   - Programma : Tipo = Dimostrazione : Enunciato
   - connettivi
   - vero e falso
   - prove di logica proposizionale
   - uguaglianza
   - prove equazionali
   - quantificatori
   - prove in logica del primo ordine

 - Esercizi

#</div># *)

From mathcomp Require Import ssreflect.


(** -------------------------------------------- *)

(** #<div class='slide'># 
** Fare una dimostrazione è come abitare un tipo *)

Definition prova1 : nat := O.
Check prova1.


(** Però lo facciamo in modo interattivo, usando
    dei comandi (tattiche) che costruiscono termini
    per noi. *)
Lemma prova2 : nat.
Proof.
apply: O.
Qed.

Print prova2.

(** I tipi (di dato) che abbiamo visto nella prima
    lezione non sono adatti a esprimere proprietà
    o enunciare veri e propri teoremi.

    Ne definiamo quindi altri... 

 #<div class="concepts">#
Concetti:
- dimostrare = costruire termini passo passo
- [Lemma nome : tipo. Proof. ...prova... Qed.]
- [apply: t] usa [t] per dimostrare il goal corrente, ovvero
  [t] è un termine che abita il tipo del goal
 #</div>#

#</div>#

*)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Connettivi *)

(** $$$$P \to Q$$$$ *)

Lemma example1 P : P -> P.
Proof.
apply: (fun (p : P) => p).
Qed.

(** dimostrare una implicazione (introduzione) *)
Lemma example2 P : P -> P.
Proof.
move=> p.
apply: p.
Qed.

(** Usare una implicazione (MP) *)
Lemma example3 P Q : Q -> (Q -> P) -> P.
Proof.
apply: (fun (q : Q) => fun (f : Q -> P) => f q).
Qed.

Lemma example4 P Q : Q -> (Q -> P) -> P.
Proof.
move=> q f.
apply: (f _).
apply: q.
Qed.

(** $$$$P \land Q$$$$ *)

Inductive and P Q := conj (p : P) (q : Q).

Infix "/\ " := and : type_scope.
Arguments conj {P Q} p q.

Lemma andC P Q : P /\ Q -> Q /\ P.
Proof.
move=> pq.
case: pq.
move=> p q.
apply: (conj _ _).
  apply: q.
apply: p.
Qed.

(** Ricordate l'esercizio 8bis? *)
Lemma andC2 P Q : P /\ Q -> Q /\ P.
Proof.
apply: (fun x => match x with conj p q => conj q p end).
Qed.

(** $$$$P \lor Q$$$$ *)

Inductive or P Q :=
  | left (p : P)
  | right (q : Q).

Arguments left {P Q} p.
Arguments right {P Q} q.
Infix "\/" := or  : type_scope.

Lemma orC P Q : P \/ Q -> Q \/ P.
Proof.
move=> pq.
case: pq.
  move=> p.
  apply: right.
  apply: p.
move=> q.
apply: left.
apply: q.
Qed.

Lemma orC2 P Q : P \/ Q -> Q \/ P.
Proof.
apply: (fun pq =>
          match pq with
          | left p => right p
          | right q => left q
          end).
Qed.

(**

 #<div class="concepts">#
 Concetti:
 - congiunzione [/\]
 - disgiunzione [\/]
 - [move=> nome]
 - [case: termine]
 #</div>#

 #</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Vero e falso *)

(** $$$$\top$$$$ *)

Inductive True := I.

Lemma exampleI : True -> True.
Proof.
move=> i.
case: i.
apply: I.
Qed.

(** $$$$\bot$$$$ *)

Inductive False := .

Lemma ex_falso P : False -> P.
Proof.
move=> abs.
case: abs.
Qed.

Lemma ex_falso2 P : False -> P.
Proof.
apply: (fun (abs : False) => match abs with end).
Qed.

(** $$$$\neg$$$$ *)

Definition not P := P -> False.

Notation "~ p" := (not p) : type_scope.

Lemma contradiction P : P -> not P -> False.
Proof.
move=> p np.
unfold not in np.
apply: (np _).
apply: p.
Qed.

(** Note: questo lemma è uguale all'esempio 4 *)

(**
 #<div class="concepts">#
 Concetti:
 - vero e falso: [True], [False]
 - negazione: [~]
 - sostituire il nome con il corpo: [unfold name in hyp]
   (passo non strettamente necessario)
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Uguaglianza 

  Ora ci siamo stufati della logica proposizionale
  e passiamo a quella del primo ordine.

  Ci serve un predicato, e partiamo dal più difficle ;-)

  Il tipo [Id] (che in Coq si chiama [eq])

*)

Inductive eq (A : Type) (a : A) : A -> Type :=
  erefl : eq A a a.

Check eq.
Check eq nat 3 4.
Check eq bool true true.
(** [forall] lega un termine *)
Check erefl.

Arguments eq {A} a _.
Arguments erefl {A} a. (* nota: solo 2 argomenti *)

Infix "=" := eq : type_scope.

Check (3 = 4).

(* Usiamo e dimostriamo un'uguaglianza *)

Lemma eq_sym_nat (x y : nat) : x = y -> y = x.
Proof.
move=> E.
rewrite E.
apply: (erefl y).
Qed.

Lemma eq_sym_nat2 (x y : nat) : x = y -> y = x.
Proof.
apply: (fun E : x = y =>
   match E (*in (_ = a) return a = x*) with
   | erefl => erefl x
   end).
Qed.

(** eq (Id) descrive una uguaglianza computazionale *)

Lemma test_computation : 3 + 2 = 5.
Proof.
apply: erefl.
Qed.

Eval compute in 3 + 2.

(**
 #<div class="concepts">#
 Concetti:
 - uguaglianza [=] (Id nelle note del corso)
 - Usare un'uguaglianza: [rewrite]
 - [erefl] dimostra [eq] per termini uguali una
   volta nomalizzati
 - tipare un [match] (la clausola [return] e
   il tipo "da fuori" e "da dentro"
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Quantificatori
 
   Piccolo ripasso:

   Il [forall] è primitivo, è stato usato
   - per legare tipi [forall A : Type, list A -> nat]
   - per legare termini [forall x : A, eq A x x]
   - per legare.. niente [A -> B = forall dummy : A, B]
   Il dominio di [forall]
   - il tipo dei tipi [forall A : Type, ..]
   - un tipo di dato [forall x : nat, ...]
   - il tipo delle funzioni [forall f : nat -> nat, ...]
*)
(**
    Ora usiamo $$$$\forall x:A, P x$$$$
    che può essere dimostrato fornendo un
    funzione che data una prova di [A] (chiamata [x])
    produce una prova di [P x] *)

Lemma test_forall : forall x : nat, x = x.
Proof.
apply: (fun x : nat => erefl x).
Qed.

Lemma test_forall2 : forall x : nat, x = x.
Proof.
move=> x.
apply: erefl x.
Qed.

(** Nota: del tutto simile alla prova di [P -> P] fatta
nella slide 2 *)

Lemma test_uso_forall :
	 (forall x : nat, x * 0 = 0) -> 3 * 0 = 0.
Proof.
move=> mulx0.
Check (mulx0 3).
apply: (mulx0 3).
Qed.

(** Nota: anche in questo caso il comportamento di XXX\forallXXX
è molto simile a quello di XXX\toXXX *)

(**
    Ora definiamo $$$$\exists x:A, P x$$$$
    che può essere dimostrato fornendo un
    testimone [t : A] e una prova [p : P t] *) 

Inductive sig (A : Type) (P : A -> Type) :=
  sigI (a : A) (p : P a).

(** Nota: è molto simile alla coppia, ma il tipo
    della seconda componente dipende val valore della
    prima *)

Check sigI.
(** [forall] lega un predicato/funzione *)
Check sig.

Check (fun x : nat => x = 3).

Arguments sig {_} _.
Arguments sigI {_ _} _ _.

Check sig (fun x => x = 3).

Notation "'exists' x : A , p" := (sig (fun x : A => p)) (at level 200, x ident).

Definition divides d n := exists q : nat, d * q = n.

Lemma div3_15 : divides 3 15.
Proof.
exists 5.
apply:erefl.
Qed.

Lemma mulnA a b c : a * (b * c) = a * b * c.
Proof.
Admitted.

Lemma div_trans a b c : divides a b -> divides b c -> divides a c.
Proof.
move=> dab dbc.
case: dab. move=> q Eb.
case: dbc. move=> p Ec.
exists (q * p).
rewrite -Ec -Eb.
rewrite mulnA.
apply: erefl.
Qed.

(** #</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Dimostrazioni per casi

*)


Lemma andbC a b : andb a b = andb b a.
Proof.
case: a.
  case: b.
    apply: erefl.
    apply: erefl.
case: b.
  apply: erefl.
apply: erefl.
(* ripetitiva no? rifacciamola con il ; *)
Qed.

(**
 #<div class="concepts">#
 Concetti:
 - [case:] funziona anche su termini che rappresentano
   dati, come [bool] e [nat]
 - [;] per combinare 2 comandi di prova
 #</div>#

#</div># *)


(** -------------------------------------------- *)

(** #<div class='slide'># 
** Discriminazione dei costruttori e sotto tipi

   - definiamo il tipo dei numeri naturali positivi
   - usiamolo per programmare la funzione [pred]

*)

Definition positivo := exists n : nat, ~ n=0.

Definition pred (x : positivo) : nat.
Proof.
case: x.
move=> n.
case: n.
  move=> abs.
  apply: (ex_falso nat).
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

Definition n3p : positivo := sigI 3 not_3_0.

Eval compute -[not] in pred n3p.

(**
 #<div class="concepts">#
 Concetti:
 - [sig] rappresenta un sotto tipo
 - [sigI] è come [pair], raggruppa due termini
   e possiamo usarlo per scrivere programmi
 - [change tipo] per cambiare la forma del goal
   corrente con una convertibile
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Prove all'avanti

*)

Lemma fwd P Q :
  (P -> Q) -> P -> ~Q -> 0 = 1.
Proof.
move=> p2q p nq.
have q : Q.
  apply: p2q. apply: p.
have abs : False.
  apply: nq. apply q.
case: abs.
Qed.

(**
#<div class="concepts">#
 Concetti:
 - [have nome : tipo] inizia una sottoprova
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class="slide">#

  ** Dimostriamo (hem programmiamo) il principio di induzione per [nat]

  Se le prove sono programmi, allora abitiamo questo tipo, senza troppo
  riflettere a cosa significhi.
*)

Fixpoint rec (P : nat -> Type) (p0 : P 0) (pS : forall n, P n -> P (S n)) (n : nat) : P n :=
  match n with
  | O => p0
  | S q => pS q (rec P p0 pS q)
  end.

Check rec.

(** Abbiamo ottenuto il principio di induzione! 

    Beh, anche Coq lo sa fare... Infatti non appena uno
    definisce i tipo [nat] Coq genera questo programma
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

  ** Relazioni induttive (e non)

  Proviamo ora ad esprimere il predicatoXXX\leqXXX
  per i numeri naturali.

  Abbiamo dues possibilità
*)

Inductive is_leq (n : nat) : nat -> Type :=
  | leqO : is_leq n n
  | leqS : forall m, is_leq n m -> is_leq n (S m).

Lemma test_is_leq : is_leq 4 6.
Proof.
apply: leqS.
apply: leqS.
apply: leqO.
Qed.

Fixpoint leq (n m : nat) : bool :=
  match n with
  | O => true
  | S a => match m with
           | O => false
           | S b => leq a b
           end
  end.

Lemma test_leq : leq 4 6 = true.
Proof.
apply: erefl.
Qed.

(** #</div># *)
(** -------------------------------------------- *)
(** #<div class="slide"># *)

(** *** Link utili:
    - #<a href="https://hal.inria.fr/inria-00258384">manuale</a># del linguaggio di prova
    - #<a href="http://www-sop.inria.fr/marelle/math-comp-tut-16/MathCompWS/basic-cheatsheet.pdf">cheat-sheet</a>#
*)

(** #</div># *)


(** #<div class='slide'>#
** Esercizi 

*)

(** -------------------------------------------- *)
(** ** Abitare i seguenti tipi (in un colpo solo o con dei comandi di prova) *)

Lemma scrambled A B C : (A /\ B) /\ C -> (C /\ A) /\ B.
Proof.
(*D*)apply: (fun x =>
(*D*)  match x with
(*D*)  | conj (conj a b) c => conj (conj c a) b
(*D*)  end).
Qed.

(** 
#
<button onclick="hide('sol1')">Soluzione</button>
<div id='sol1' class='solution'>
<pre>
apply: (fun x =>
match x with
| conj (conj a b) c => conj (conj c a) b
end).
</pre>
</div>
#
*)

Lemma eggs P Q R : (P \/ Q -> R) -> Q -> R.
Proof.
(*D*)apply: (fun f q => f (right q)).
Qed.

(** 
#
<button onclick="hide('sol2')">Soluzione</button>
<div id='sol2' class='solution'>
<pre>
apply: (fun f q => f (right q)).
</pre>
</div>
#
*)

Lemma DM P Q : (~ P /\ ~ Q) -> ~ (P \/ Q).
Proof.
(*D*)move=> npnq. case: npnq => np nq.
(*D*)move=> poq. case: poq. apply: np. apply: nq.
Qed.

(** 
#
<button onclick="hide('sol3')">Soluzione</button>
<div id='sol3' class='solution'>
<pre>
move=> npnq. case: npnq => np nq.
move=> poq. case: poq. apply: np. apply: nq.
</pre>
</div>
#
*)

(** #<a href="https://en.m.wikipedia.org/wiki/Peirce's_law">La formula di Peirce</a># 

 - Suggerimento: scegliere per [Q] una formula falsa!
*)

Lemma Peirce :
  (forall Q P, (((P -> Q) -> P) -> P)) ->
  (forall P, P \/ ~ P).
Proof.
(*D*)move=> cc P.
(*D*)apply: (cc False).
(*D*)move=> truth.
(*D*)apply: right.
(*D*)move=> p.
(*D*)apply: truth.
(*D*)apply: left.
(*D*)apply: p.
Qed.
 
(** 
#
<button onclick="hide('sol4')">Soluzione</button>
<div id='sol4' class='solution'>
<pre>
move=> cc P.
apply: (cc False).
move=> truth.
apply: right.
move=> p.
apply: truth.
apply: left.
apply: p.
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** ** Dimostrare che [orb] è commutativo *)

Definition orb b1 b2 :=
  match b1 with
  | true => true
  | false => b2
  end.

Lemma orbC b1 b2 : orb b1 b2 = orb b2 b1.
Proof.
(*D*)case: b1; case: b2; apply: erefl.
Qed.

(** 
#
<button onclick="hide('sol5')">Soluzione</button>
<div id='sol5' class='solution'>
<pre>
case: b1; case: b2; apply: erefl.
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** ** Dimostrare che [orb] è associativo *)

Lemma orbA b1 b2 b3 : orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
Proof.
(*D*) case: b1; case: b2; case: b3; apply: erefl.
Qed.

(** 
#
<button onclick="hide('sol6')">Soluzione</button>
<div id='sol6' class='solution'>
<pre>
case: b1; case: b2; case: b3; apply: erefl.
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** ** Dimostrare il seguente lemma *)

Lemma EMb b : orb b (negb b) = true.
Proof.
(*D*)case: b; apply: erefl.
Qed.

(** 
#
<button onclick="hide('sol7')">Soluzione</button>
<div id='sol7' class='solution'>
<pre>
case: b; apply: erefl.
</pre>
</div>
#
*)


(** -------------------------------------------- *)
(** ** Dimostra la seguente formula 

XXX
  m ^ 2 - n ^ 2 =  (m - n) * (m + n)
XXX

   Usare solo la riscrittura [rewrite]
   e i seguenti simboli e lemmi che sono forniti

*)

Variable subn : nat -> nat -> nat.
Infix "-" := subn.
Variable expn : nat -> nat -> nat.
Infix "^" := expn.
Lemma mulnBl (x y z : nat) : (x - y) * z = x * z - y * z. Admitted.
Lemma mulnDr (x y z : nat) : x * (y + z) = x * y + x * z. Admitted.
Lemma addnC (x y : nat) : x + y = y + x. Admitted.
Lemma mulnC (x y : nat) : x * y = y * x. Admitted.
Lemma subnDl (p m n : nat) : p + m - (p + n) = m - n. Admitted.
Lemma mulnn n : n * n = n ^ 2. Admitted.


(** Traccia della prova
<<
(m - n) * (m + n) =
          .. = m * (m + n) - n * (m + n)
          .. = m * m + m * n - n * (m + n)
          .. = m * m + m * n - (n * m + n * n)
          .. = m * n + m * m - (n * m + n * n)
          .. = n * m + m * m - (n * m + n * n)
          .. = m * m - n * n
          .. = m ^ 2 - n * n
          .. = m ^ 2 - n ^ 2
>> *)

Lemma subn_sqr m n : (m - n) * (m + n) = m ^ 2 - n ^ 2.
Proof.
(*D*)rewrite mulnBl.
(*D*)rewrite mulnDr.
(*D*)rewrite mulnDr.
(*D*)rewrite addnC.
(*D*)rewrite mulnC.
(*D*)rewrite subnDl.
(*D*)rewrite mulnn.
(*D*)rewrite mulnn.
(*D*)apply: erefl.
Qed.

(** 
#
<button onclick="hide('sol8')">Soluzione</button>
<div id='sol8' class='solution'>
<pre>
rewrite mulnBl.
rewrite mulnDr.
rewrite mulnDr.
rewrite addnC.
rewrite mulnC.
rewrite subnDl.
rewrite mulnn.
rewrite mulnn.
apply: erefl.
</pre>
</div>
#
*)


(** #</div># *)

(** ------------------------------------------------------ *)

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
