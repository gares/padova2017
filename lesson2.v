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

Infix "/\" := and : type_scope.
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

(** $$$$P \or Q$$$$ *)

Inductive or P Q :=
  | left (p : P)
  | right (q : Q).

Arguments left {P Q} p.
Arguments right {P Q} q.
Infix "\/" := or : type_scope.

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

(** $$$$\bot$$$$) *)

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

(** $$$$\lneg$$$$ *)

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

*)

Universe i. (* hum, perdonate il dettaglio tecnico *)

Inductive Id (A : Type) (a : A) : A -> Type@{i} :=
  refl : Id A a a.

Check Id.
Check Id nat 3 4.
Check Id bool true true.
(** [forall] lega un termine *)
Check refl.

Arguments Id {A} a _.
Arguments refl {A} a. (* nota: solo 2 argomenti *)

Infix "=" := Id : type_scope.

Check (3 = 4).

(* Usiamo e dimostriamo un'uguaglianza *)

Lemma Id_sym_nat (x y : nat) : x = y -> y = x.
Proof.
move=> E.
rewrite E.
apply: (refl y).
Qed.

Lemma Id_sym_nat2 (x y : nat) : x = y -> y = x.
Proof.
apply: (fun E : x = y =>
   match E (*in (_ = a) return a = x*) with
   | refl => refl x
   end).
Qed.

(** Id descrive una uguaglianza computazionale *)

Lemma test_computation : 3 + 2 = 5.
Proof.
apply: refl.
Qed.

Eval compute in 3 + 2.

(**
 #<div class="concepts">#
 Concetti:
 - Id [=]
 - Usare un'uguaglianza: [rewrite]
 - [refl] dimostra [Id] per termini uguali una
   volta nomalizzati
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
    Ora definiamo $$$$\exists x:A, P x$$$$
    che può essere dimostrato fornendo un
    testimone [t : A] e una prova [p : P t] *) 

Inductive ex (A : Type) (P : A -> Type) :=
  exI (a : A) (p : P a).

(** Nota: è molto simile alla coppia, ma il tipo
    della seconda componente dipende val valore della
    prima *)

Check exI.
(** [forall] lega un predicato/funzione *)
Check ex.

Check (fun x : nat => x = 3).

Check ex nat (fun x => x = 3).

Notation "'exists' x : A , p" := (ex A (fun x : A => p)) (at level 200, x ident).

Definition divides d n := exists q : nat, d * q = n.

Lemma div_mul a b : divides a (a * b).
Proof.
exists b.
apply: refl.
Qed.

Require Import Arith.

Lemma div_trans a b c : divides a b -> divides b c -> divides a c.
Proof.
move=> dab dbc.
case: dab. move=> q Eb.
case: dbc. move=> p Ec.
exists (q * p).
rewrite -Ec -Eb.
Search (_ * _ * _).
rewrite Nat.mul_assoc.
apply: refl.
Qed.


(**
 #<div class="concepts">#
 Concetti:
 - [exists T P] non è altro che [/\] ovvero la coppia
   ma dove il tipo della seconda componente dipende dal
   valore della prima
 - lo dimostriamo col comando [exists] (senza i [:])
 - lo usiamo con [case:]
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Dimostrazioni per casi

*)


Lemma andbC a b : andb a b = andb b a.
Proof.
case: a.
  case: b.
    apply: refl.
    apply: refl.
case: b.
  apply: refl.
apply: refl.
(* ripetitiva no? *)
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



(** #<div class='slide'>#
** Esercizi 

*)

(** -------------------------------------------- *)
(** Abitare i seguenti tipi (in un colpo solo o con dei
    comandi di prova) *)

Lemma scrambled A B C : (A /\ B) /\ C -> (C /\ A) /\ B.
Proof.
apply: (fun x =>
  match x with
  | conj (conj a b) c => conj (conj c a) b
  end).
Qed.

Lemma eggs P Q R : (P \/ Q -> R) -> Q -> R.
Proof.
apply: (fun f q => f (right q)).
Qed.

Lemma DM P Q : (~ P /\ ~ Q) -> ~ (P \/ Q).
Proof.
move=> npnq. case: npnq => np nq.
move=> poq. case: poq. apply: np. apply: nq.
Qed.

(* link to wikipedia *)

Lemma Peirce :
  (forall Q P, (((P -> Q) -> P) -> P)) ->
  (forall P, P \/ ~ P).
Proof.
move=> cc P.
apply: (cc False).
move=> truth.
apply: right.
move=> p.
apply: truth.
apply: left.
apply: p.
Qed.
 

(** -------------------------------------------- *)
(** Dimostrare che [orb] è commutativo *)

Definition orb b1 b2 :=
  match b1 with
  | true => true
  | false => b2
  end.

Lemma orbC b1 b2 : orb b1 b2 = orb b2 b1.
Proof.
case: b1; case: b2; apply: refl.
Qed.

(** -------------------------------------------- *)
(** Dimostrare che [orb] è associativo *)

Lemma orbA b1 b2 b3 : orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
Proof.
case: b1; case: b2; case: b3; apply: refl.
Qed.

(** -------------------------------------------- *)
(** Dimostrare il seguente lemma *)

Lemma EMb b : orb b (negb b) = true.
Proof.
case: b; apply: refl.
Qed.


(** 
#
<button onclick="hide('sol1')">Solution</button>
<div id='sol1' class='solution'>
<pre>
...
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
