(** #<div class='slide vfill'>#  
** Lezione 4

 - Riflessione computazionale
   - idea
   - normalizzazione nella segnatura di
     un monoide

 - Applicazioni di Coq
   - un compilatore C verificato
   - un libreria di matematica organizzata
     come una libreria di programmi 

 - Esercizi

#</div># *)

From mathcomp Require Import all_ssreflect.


(** ----------------------------------- *)

(** #<div class='slide'># 
** 
   Bello:
   - nella teoria dei tipi dimostrare [2+3=3+2] è facile,
     o meglio, la dimostrazione è _molto_ corta [apply: refl]
   - tale dimostrazione non dipende dalla taglia delle espressioni
     coinvolte, ie rimane triviale anche per [2+3+4+5=5+2+3+4]
   Meno bello:
   - il calcollo è completo su termini chiusi, se sono presenti
     variabili dobbiamo rgionare per induzione o riutilizzare lemmi
     dimostrati in precendenza, eg [x + 0 = x]
   - la taglia della dimostrazione dipende però dal numero di passi
     da fare, eg [(x + 0) + 0 = x] richiede 2 riscritture

   Osservazione:
   - l'esecuzione di un programma [p] non richiede una prova
     [p x = y]
   - e non importa quanti "passi" di esecuzione [p] faccia
     la prova di [p x = y] è sempre [refl]

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

Lemma norm_ok_example :
  interp addn 0 example = interp addn 0 (norm example).
Proof.
apply: (erefl (3+2)).
Qed.

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

Lemma test x y :
  x + (y + 0) + 0 = x + y.
Proof.
pose s := Op (Op (Value x) (Op (Value y) Identity)) Identity.
change (interp addn 0 s = x+y).
rewrite (norm_ok addnA add0n addn0).
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

  Fortna: non ci interessa dimostrarla corretta, basta
  che lo sia in pratica.

*)

Ltac quote t :=
  match t with
  | (?a + ?b) =>
        let x := quote a in
        let y := quote b in
        uconstr:(Op x y)
  | 0 => uconstr:(Identity)
  | ?x => uconstr:(Value x)
  end.

Ltac monoid :=
  match goal with
  |- ?a = ?b =>
      let x := quote a in
      let y := quote b in 
      change (interp addn 0 x = interp addn 0 y);
      rewrite [interp addn 0 x](norm_ok addnA add0n addn0);
      rewrite [interp addn 0 y](norm_ok addnA add0n addn0);
      compute -[addn]
  end.

Lemma test2 x y :
  x + (y + 0) + 0 = 0 + x + y. 
Proof.
monoid.
apply: erefl.
Qed.

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Applicazione: Compilatore certificato CompCert 
*)

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Applicazione: Verfica di prove di matematica 
*)

(** #</div># *)

(** ----------------------------------- *)

(** #<div class='slide'># 
** Esercizio: 

   aggiungere un elemento assorbente
   al monoide (sintassi, interpretazione, normalizzazione
   e prova di correttezza) 
*)

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
