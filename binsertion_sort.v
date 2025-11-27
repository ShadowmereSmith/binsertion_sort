(** PROJETO E ANÁLISE DE ALGORITMOS - 2025/2 *)
(** Link do site do coq se vocês prefirirem: https://jscoq.github.io/scratchpad.html

Nome e username dos participantes:
1. 
2. Geilson - Geilsondss 
3. 
*)
   
   (** *Correção do algoritmo mergesort *)

(** O algoritmo mergesort é um algoritmo de ordenação que utiliza a técnica de divisão e conquista, que consiste das seguintes etapas:
Divisão: O algoritmo divide a lista l recebida como argumento ao meio, obtendo as listas l_1 e l_2. 
Conquista: O algoritmo é aplicado recursivamente às listas l_1 e l_2 gerando, respectivamente, as listas ordenadas l_1' e l_2'.
Combinação: O algoritmo combina as listas l_1' e l_2' através da função merge que então gera a saída do algoritmo.
Por exemplo, ao receber a lista (4 :: 2 :: 1 :: 3 :: nil), este algoritmo inicialmente divide esta lista em duas sublistas, a saber (4 :: 2 :: nil) e (1 :: 3 :: nil). O algoritmo é aplicado recursivamente às duas sublistas para ordená-las, e ao final deste processo, teremos duas listas ordenadas (2 :: 4 :: nil) e (1 :: 3 :: nil). Estas listas são, então, combinadas para gerar a lista de saída (1 :: 2 :: 3 :: 4 :: nil). *))

Require Import Arith List Recdef.
Require Import Coq.Program.Wf.
Require Import Permutation.
(* end hide *)



Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).



Definition le_all x l := forall y, In y l -> x <= y.

(* begin hide *)
Infix "<=*" := le_all (at level 70, no associativity).
(* end hide *)


Lemma tail_sorted: forall l a, sorted (a :: l) -> sorted l.
(* begin hide *)
Proof.
  Admitted.


(* end hide *)


Lemma le_all_sorted: forall l a, a <=* l -> sorted l -> sorted (a :: l).
Proof.
  Admitted.
      

Lemma remove_sorted: forall l a1 a2, sorted (a1 :: a2 :: l) -> sorted (a1 :: l).
(* begin hide *)
Proof.
  Admitted.
(* end hide *)


Lemma sorted_le_all: forall l a, sorted(a :: l) -> a <=* l.
Proof.
  Admitted.


Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl
  end.


Definition perm l l' := forall n:nat, num_oc n l = num_oc n l'.


Lemma perm_refl: forall l, perm l l.
(* begin hide *)
Proof.
Admitted.
(* end hide *)


Lemma num_oc_append: forall n l1 l2, num_oc n l1 + num_oc n l2 = num_oc n (l1 ++ l2).
(* begin hide *)
Proof.
  Admitted.
(* end hide *)


Definition sorted_pair_lst (p: list nat * list nat) :=
sorted (fst p) /\ sorted (snd p).


Definition len (p: list nat * list nat) :=
   length (fst p) + length (snd p).

(* printing *)

Function merge (p: list nat * list nat) {measure len p} :=
match p with
  | (nil, l2) => l2
  | (l1, nil) => l1
  | ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
      else hd2 :: merge (l1, tl2)
   end.

(* begin hide *)
Proof.
  Admitted.
(* end hide *)


Lemma merge_in: forall y p, In y (merge p) -> In y (fst p) \/ In y (snd p).
(* begin hide *)
Proof.
Admitted.
(* end hide *)


Theorem merge_sorts: forall p, sorted_pair_lst p -> sorted (merge p).
(* begin hide *)
Proof.
  Admitted.

(* end hide *)


Function mergesort (l: list nat) {measure length l}:=
  match l with
  | nil => nil
  | hd :: nil => l
  | hd :: tail =>
     let n := length(l) / 2 in
     let l1 := firstn n l in
     let l2 := skipn n l in
     let sorted_l1 := mergesort(l1) in
     let sorted_l2 := mergesort(l2) in
     merge (sorted_l1, sorted_l2)
  end.

(* begin hide *)
Proof.
Admitted.
(* end hide *)


Theorem mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  Admitted.


Lemma merge_num_oc: forall n p, num_oc n (merge p) = num_oc n (fst p) + num_oc n (snd p).
(* begin hide *)
Proof.
Admitted.
(* end hide *)


Theorem mergesort_is_perm: forall l, perm l (mergesort l).
Proof.
  Admitted.


Theorem mergesort_is_correct: forall l, perm l (mergesort l) /\ sorted (mergesort l).
Proof.
  Admitted.
