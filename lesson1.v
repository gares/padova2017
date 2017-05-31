(** #<div class='slide vfill'>#  
** Lezione 1

 - Coq: un linguaggio di programmazione funzionale
   - funzioni anonime e non
   - valutazione di funzioni
   - tipi di dato algebrici
   - pattern matching
   - ricorsione
   - tipi di dato polimorfi
   - ordine superiore
   - calcolo simbolico

 - Esercizi

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Funzioni

Prendiamo come esempio la definizione di una
semplice funzione aritmetica [f]:

$$$$ 
f = x \mapsto x + 1
$$$$
$$$$
f : \mathcal{N} \to \mathcal{N}
$$$$

e traduciamola in Coq.

*)

Check (fun (x : nat) => x + 1).

Definition f (x : nat) : nat :=
  x + 1.

Definition g (x : nat) (y : nat) : nat :=
  f x * y.

(**

 Nota: anche se [nat], [+], [*] e [1] sono concetti definibili
  in Coq, l'ambiente iniziale non è vuoto ma contiene
  alcuni declarazioni utili a fare esempi come i numeri
  naturali e le operazioni di addizione e moltiplicazione

 #<div class="concepts">#
 Concetti:
  - funzione anonima [fun]
  - definizione con nome [Definition]
  - sintassi per l'applicazione
  - comando [Check] per chiedere il tipo di un termine
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Valutazione di funzioni (calcolo, esecuzione)

  In Coq funzione = programma, ovvero le funzioni
  definite vengono calcolate (eseguite) quando il
  loro input è noto.

  Chiediamo a Coq di calcolare _la forma canonica_
  dei termini seguenti:
*)

Eval compute in 3 + 1.


(** Esempio di XXX\betaXXX-riduzione (sostituzione di x
    con l'argomento) *)
Eval compute in (fun x => x + 1) 3.

(** In questi due esempi f e g (nomi) sono sostituiti con i
    propri valori  *)
Eval compute in f 3.

Eval compute in g 3 4.

(**
 #<div class="concepts">#
 Concetti:
 - esecuzione di programmi [Eval compute in]
 #</div>#
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Tipi di dato algebrici

 Facciamo finta che i numeri naturali
 che abbiamo usato finora non siano disponibili
 e definiamoli noi.  Lo facciamo dentro un [Module],
 una specie di contenitore per evitare che Coq faccia
 confusione tra
 i concetti già esistenti e quelli che stiamo definendo.
*)

Module ProvaBoolNat.

Inductive bool := true | false.

(** true e false si chiamano costruttori, e
    corrispondono alle regole XXXTipo-I_nXXX
    nelle note del corso *)

Check true.

(** I numeri naturali à la Peano

    Nota: _O_ è una o maiuscola, non la cifra zero *)
Inductive nat := O | S (n : nat).

Check O.
Check S.

Check (S O).

(** Nota: esistono varie sintassi alternative per
    la dichiarazione di tipi di dato.

  Quella che abbiamo utilizzato è la più simile a quella
  usata nelle note del corso (e anche nei linguaggi di
  programmazione).  Se chiediamo a Coq di stampare una
  dichiarazione di tipo con:

*)

Print nat.

(** otteniamo la stampa in una sintassi alternativa. *)

End ProvaBoolNat.

(** Ora torniamo a utilizzare la dichiarazione standard di
    _nat_ in quanto il sistema li stampa/parsa meglio
   (notazione decimale).
*)

Print nat.
Check (S O).
Set Printing All.
Check (S O).
Unset Printing All.
Check (S O).

(**

 #<div class="concepts">#
 Concetti:
 - dichiarazione tipo induttivo [Inductive]
 - comando per stampare una dichiarazione induttiva [Print]
 - notazioni decimali per [nat], e.g. [1 = S O]
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Pattern matching

 - In Coq l'eliminatore (chiamato XXXElXXX nelle note
   del corso) è fornito in _kit_:
   - il costrutto [match] fornisce l'analisi per casi
   - il costrutto [Fixpoint] (in seguito) fornisce
     "l'ipotesi induttiva"
 - Inoltre le regole computazionali dell'eliminatore
   sono date dalla combinazione
     di [match] e [Fixpoint]

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

(** Definiamo ora il predecessore *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S p => p
  end.

Eval compute in pred 3.


(**
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

Eval compute in pred O.

(** 
  Note:
  - Ogni clausola del pattern matching è della forma
    [| pattern => corpo]
    dove pattern è un costruttore applicato a un numero
    di variabili appropriato
  - Tutti i costruttori del tipo di dato devono essere
    trattati da un pattern (eg anche il caso [O] per [pred])
  - _p_ è una variabile legata dal pattern matching
    e può essere utilizzata nel corpo della clausola
  - il termine a cui il [match] è applicato viene
    messo in forma canonica. In altre parole i casi del
    [match] parlano della forma canonica. *)
Eval compute in
  match 2 + 1 with
  | O => O
  | S m => m
  (* non è un caso "A + B" e via dicendo *) 
  end.

(**

 #<div class="concepts">#
 Concetti:
 - pattern matching [match .. with .. end]
 - forma delle clausole [K x => v] dove [K] è un costruttore
 - calcolo di una funzione definita via pattern matching
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Ricorsione

Definiamo l'addizione sui numeri naturali.

$$$$
 0 + m = m
$$$$
$$$$
S~p + m = S (p + m)
$$$$

*)

Fixpoint addn (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S p => S (addn p m)
  end.

Eval compute in addn 2 4.

(** Esempio di esecuzione:
<<
  addn 2 
  addn (S (S O)) 4
  S (addn (S O) 4)
  S (S (addn O 4))
  S (S 4)
  6
>>

Non tutti i programmi ricorsivi sono accettati! *)

Fail
  Fixpoint loop (n : nat) : bool := loop n.

(** 

 #<div class="concepts">#
Concetti:
  - programmi ricorsivi [Fixpoint]
  - terminazione
 #</div>#

#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Tipi di dato polimorfi

 I tipi di dato polimorfi sono, in genere, dei contenitori
 per aggregare vari termini. Inoltre vogliamo spesso
 riutilizzare tali contenitori per aggregare termini
 di tipo di volta in volta diverso.

 Esempi classici:
 - La coppia XXX(a,b)XXX dove XXXa : AXXX e XXXb : BXXX
 - La lista XXXx_1 :: \ldots :: x_nXXX dove XXXx_i : AXXX

*)


Inductive prod (A : Type) (B : Type) :=
  | pair (a : A) (b : B).

Check prod.
Check prod nat bool.
Check pair.

(** [forall A B : Type], ci indica che [pair] è polimorfo,
    ovvero A e B possono essere rimpiazzati per tipi di dato
    a piacere *)

Check pair nat bool.
Check pair nat bool 3 false.
Check pair nat nat 4 5.

(** Come assegnare il tipo a una applicazione
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

(** 
 #<div class="concepts">#
Concetti:
  - polimorfismo e quantificazione [forall A : Type]
  - tipaggio dell'applicazione in presenza di [forall]
  - pattern matching e parametri di tipo
 #</div>#

#</slide># *)

(** ---------------------------------------- *)

(** #<div class='slide'># 
** Argomenti impliciti (inferiti da Coq) 

  I termini costruiti in precedenza, come
   [pair nat bool 3 false]
  sono molto verbosi e contengono informazione ridondante.

*)

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

(** 
 #<div class="concepts">#
Concetti:
    - argomenti impliciti (inferenza)
 #</div>#
#</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Liste (omogenee) e notazione

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

Infix "::" := cons.

Check 2 :: 3 :: nil.
Set Printing All.
Check 2 :: 3 :: nil.
Unset Printing All.

Fixpoint rcons {A} (l : list A) (a : A) : list A :=
  match l with
  | nil => a :: nil
  | x :: xs => x :: rcons xs a
  end.

Eval compute in rcons (1 :: 2 :: nil) 3.

Notation "a + b" := (addn a b) : nat_scope.

(**
 #<div class="concepts">#
Concetti:
- liste
- notazioni infisse
- parametri tra [{}] sono impliciti
 #</div>#

 #</div># *)

(** -------------------------------------------- *)

(** #<div class='slide'># 
** Ordine superiore e calcolo simbolico

  Le funzioni possono essere passate ad altre funzioni
  come argumenti

  iter f 3 x = f (f (f x))

*)

Fixpoint iter {A} (f : A -> A) (n : nat) (a : A) : A :=
  match n with
  | O => a
  | S p => f (iter f p a)
  end.

Eval compute in iter S 4 3.

Definition iadd n m := iter S n m.

(** Incomincia il mal di testa ... *)
Eval compute in iter (iadd 3) 4 0.

Definition imult n m := iter (iadd n) m 0.

Eval compute in iter (imult 2) 5 1.

Definition exp b e := iter (imult b) e 1.

(** L'ordine superiore è comodo per definire
    iteratori su tipi di dato polimorfi 

    fold f (a :: b :: c) x = f c (f b (f a x))
*)

Fixpoint fold {A B} (f : A -> B -> B) (l : list A) (b : B) : B :=
  match l with
  | nil => b
  | x :: xs => fold f xs (f x b)
  end.

Eval compute in fold addn (1 :: 2 :: 3 :: nil) 0.


(** Ora chiediamo a Coq di considerare [addn] come un simbolo
    privo di corpo *)

Eval compute -[addn] in fold addn (1 :: 2 :: 3 :: nil) 0.

(** Coq è in grado di calcolare in modo simbolico ([addn] è
    momentaneament un simbolo). Ciò significa che il
    comportamento di [fold] non dipende da [f] e che, nella
    lezione 3, potremo dimostrare proprietà di [fold] valide
    per ogni [f] *)

(**  
 #<div class="concepts">#
Concetti:
 - ordine superiore
 - calcolo simbolico 
 #</div>#

#</div># *)


(** -------------------------------------------- *)

(** #<div class="slide vfill">#
** Wrap up

 - funzioni anonime: [fun x : nat => x + 1]
 - tipi di dato: [Inductive nat := O | S (n : nat)]
 - pattern matching: [match x with O => .. | S p => ..]
 - ricorsione: [Fixpoint addn n m := ...]
 - polymorfismo: [Inductive pair (A B : Type) := ..]
 - argomenti impliciti: [Check pair 2 3]
 - funzioni di ordine superiore e calcolo simbolico

 #</div># *)
(** -------------------------------------------- *)

(** #<div class='slide'>#
** Esercizi 
*)

(** 1: Scrivere la funzione anonima 
       $$$$ x \mapsto \mathrm{notb}(\mathrm{notb}~x) $$$$
       $$$$ \mathcal{B} \to \mathcal{B} $$$$
     e verificarne il tipo. *)

(*D*) Check (fun (b : bool) => notb (notb b)).

(** 
#
<button onclick="hide('sol1')">Soluzione</button>
<div id='sol1' class='solution'>
<pre>
Check (fun (b : bool) => notb (notb b)).
</pre>
</div>
#
*)
(** -------------------------------------------- *)
(** 2: Dare il nome [neg2] alla funzione precedente
       e calcolarla con input [true] e poi
       con input [false]. *)

(*D*) Definition neg2 := (fun (b : bool) => notb (notb b)).
(*D*) Eval compute in neg2 true.
(*D*) Eval compute in neg2 false.

(** 
#
<button onclick="hide('sol2')">Soluzione</button>
<div id='sol2' class='solution'>
<pre>
Definition neg2 := (fun (b : bool) => notb (notb b)).
Eval compute in neg2 true.
Eval compute in neg2 false.
</pre>
</div>
#
*)
(** -------------------------------------------- *)
(** 3: Definire il tipo di dato [bussola] con
       costruttori [Nord], [Sud], [Est], [Ovest]. *)

(*D*) Inductive bussola := Nord | Sud | Est | Ovest.

(** 
#
<button onclick="hide('sol3')">Soluzione</button>
<div id='sol3' class='solution'>
<pre>
Inductive bussola := Nord | Sud | Est | Ovest.
</pre>
</div>
#
*)
(** -------------------------------------------- *)
(** 4: Definire la funzione [isNord] che data una bussola
       restituisce il booleano [true] se e solo se
       la direzione è nord *)

(*D*) Definition isNord b := match b with Nord => true | _ => false end.

(** 
#
<button onclick="hide('sol4')">Soluzione</button>
<div id='sol4' class='solution'>
<pre>
Definition isNord b := match b with Nord => true | _ => false end.
</pre>
Nota: [_ => ..] significa "in tutti gli altri casi.."
</div>
#
*)
(** -------------------------------------------- *)
(** 5: Definire la funzione [xorb] che dati due booleani
       restituisce [true] se e solo se uno dei due è [true].
       Eseguire la funzione con input [true true] e [false true] *)

(*D*) Definition xorb b1 b2 :=
(*D*)   match b1 with
(*D*)   | false => b2
(*D*)   | true => notb b2 end.
(*D*) Eval compute in xorb true true.
(*D*) Eval compute in xorb false true.

(** 
#
<button onclick="hide('sol5')">Soluzione</button>
<div id='sol5' class='solution'>
<pre>
Definition xorb b1 b2 :=
  match b1 with
  | false => b2
  | true => notb b2 end.
Eval compute in xorb true true.
Eval compute in xorb false true.
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** 6: Scrivere la funzione ricorsiva [eqn] che
    prende due numeri di tipo [nat] e restituisce [true]
    se e solo se i due numeri sono uguali. Testare la funzione.
     *)

(*D*) Fixpoint eqn n1 n2 := 
(*D*)   match n1 with
(*D*)   | O => match n2 with O => true | S _ => false end
(*D*)   | S p1 => match n2 with O => false | S p2 => eqn p1 p2 end end.
(*D*) Eval compute in eqn 3 4.
(*D*) Eval compute in eqn 3 3.

(** 
#
<button onclick="hide('sol6')">Soluzione</button>
<div id='sol6' class='solution'>
<pre>
Fixpoint eqn n1 n2 := 
  match n1 with
  | O => match n2 with O => true | S _ => false end
  | S p1 => match n2 with O => false | S p2 => eqn p1 p2 end end.
Eval compute in eqn 3 4.
Eval compute in eqn 3 3.
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** 7: Scrivere la funzione ricorsiva [leqn] che
    prende due numeri di tipo [nat] e restituisce [true]
    se e solo se il primo numero è minore o uguale al secondo.
    Testare la funzione.
     *)

(*D*) Fixpoint leqn n1 n2 := 
(*D*)   match n1 with
(*D*)   | O => true
(*D*)   | S p1 => match n2 with O => false | S p2 => leqn p1 p2 end end.
(*D*) Eval compute in leqn 3 4.
(*D*) Eval compute in leqn 4 3.

(** 
#
<button onclick="hide('sol7')">Soluzione</button>
<div id='sol7' class='solution'>
<pre>
Fixpoint leqn n1 n2 := 
  match n1 with
  | O => true
  | S p1 => match n2 with O => false | S p2 => leqn p1 p2 end end.
Eval compute in leqn 3 4.
Eval compute in leqn 4 3.
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** 8: Definire la funzione [odd] che restituisce [true]
       se e solo se il numero naturale in input è dispari.
     *)

(*D*) Fixpoint odd n := 
(*D*)   match n with
(*D*)   | O => false
(*D*)   | S O => true
(*D*)   | S (S p) => odd p end.
(*D*) Eval compute in odd 3.
(*D*) Eval compute in odd 4.

(** 
#
<button onclick="hide('sol8')">Soluzione</button>
<div id='sol8' class='solution'>
<pre>
Fixpoint odd n := 
  match n with
  | O => false
  | S O => true
  | S (S p) => odd p end.
Eval compute in odd 3.
Eval compute in odd 4.
</pre>

Nota: la sintassi concreta di Coq permette di scrivere
pattern-match profondi.  Non è altro che una notazione.
Nel caso predente è espansa in
<pre>
Fixpoint odd n := 
  match n with
  | O => false
  | S q =>
    match q with
    | O => true
    | S p => odd p end end.

</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** 8bis: Definire la funzione [swap] che prende
       una coppia (di tipo [prod A B]) e restituisce
       la coppia dove gli argomenti sono invertiti (di tipo
       [prod B A].
     *)

(*D*) Definition swap {A B} (x : prod A B) := 
(*D*)   match x with
(*D*)   | pair a b => pair b a
(*D*)   end.


(** 
#
<button onclick="hide('sol8x')">Soluzione</button>
<div id='sol8x' class='solution'>
<pre>
Definition swap {A B} (x : prod A B) := 
   match x with
   | pair a b => pair b a
   end.
</pre>
</div>
#
*)


(** -------------------------------------------- *)
(** 9: Definire la funzione [filter] che prende
       una lista (di tipo [A]) una funzione di tipo
       [(A -> bool)] e restituisce la lista degli elementi
       sui quali la funzione restituisce [true].
       Testare [filter odd (1 :: 2 :: 3 :: nil)].
     *)

(*D*) Fixpoint filter {A} (f : A -> bool) l := 
(*D*)   match l with
(*D*)   | nil => nil
(*D*)   | x :: xs =>
(*D*)       let ys := filter f xs in
(*D*)       match f x with
(*D*)       | true => x :: ys
(*D*)       | false => ys end end.
(*D*) Eval compute in filter odd (1 :: 2 :: 3 :: nil).

(** 
#
<button onclick="hide('sol9')">Soluzione</button>
<div id='sol9' class='solution'>
<pre>
Fixpoint filter {A} (f : A -> bool) l := 
  match l with
  | nil => nil
  |  x :: xs =>
      let ys := filter f xs in
      match f x with
      | true =>  x :: ys
      | false => ys end end.
Eval compute in filter odd (1 :: 2 :: 3 :: nil).
</pre>

Nota: la sintassi [let nome := espressione in ..]
permette di dare un nome a una espression al fine di
non dovere ripetere l'espressione (potenzialmente 
grande) in quanto segue.

</div>
#
*)

(** -------------------------------------------- *)
(** 10: Definire la funzione ricorsiva [rev] che prende
       una lista [l] (di tipo [A]) e restituisce la lista 
       degli elementi di [l] in ordine inverso.
       Nota: è possibile definire una funzione ausiliaria.
       Testare la funzione.
     *)

(*D*) Fixpoint rev_aux {A} (l : list A) (acc : list A) := 
(*D*)   match l with
(*D*)   | nil => acc
(*D*)   | x :: xs => rev_aux xs (x :: acc) end.
(*D*) Definition rev {A} (l : list A) := rev_aux l nil.
(*D*) Eval compute in rev (1 :: 2 :: 3  :: nil).

(** 
#
<button onclick="hide('sol10')">Soluzione</button>
<div id='sol10' class='solution'>
<pre>
Fixpoint rev_aux {A} (l : list A) (acc : list A) := 
  match l with
   | nil => acc
   | x :: xs => rev_aux xs (x :: acc) end.
Definition rev {A} (l : list A) := rev_aux l nil.
Eval compute in rev (1 :: 2 :: 3 :: nil).
</pre>
</div>
#
*)

(** -------------------------------------------- *)
(** 11: Definire la funzione [rev] usando [fold].
    (Questa volta chiamiamola [rev2]).
    Dichiarare che il primo argomento di [rev2] (il tipo [A])
    è implicito. Testare la funzione.
*)


(*D*) Definition rev2 {A} (l : list A) := fold cons l nil.
(*D*) Eval compute in rev2 (1 :: 2 :: 3 :: nil).

(** 
#
<button onclick="hide('sol11')">Soluzione</button>
<div id='sol11' class='solution'>
<pre>
Definition rev2 {A} (l : list A) := fold cons l nil.
Eval compute in rev2 (1 :: 2 :: 3 :: nil).
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
