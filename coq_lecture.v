(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

Set Implicit Arguments.

Require Import Lia.

(*
Inductive nat : Type :=
| O
| S (n : nat)
.
*)

Fixpoint sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => n + sum m
  end.

Compute sum 100.


Theorem sum_calc: forall n: nat, 2 * sum n = n * (n+1).
Proof.
  induction n.
  - simpl. auto.
  - simpl. nia.
Qed.

Print sum_calc.

Check (eq_refl: 1 + 1 = 2).

Theorem one_plus_one_is_two: 1 + 1 = 2.
Proof.
  auto.
Qed.

Print one_plus_one_is_two.



(***
    Curry-Howard Isomorphism
 ***)

Inductive and (P Q : Type) : Type :=
| conj (p: P) (q: Q)
.

Notation "A /\ B" := (and A B) : type_scope.

Inductive or (P Q : Type) : Type :=
| or_introl (p: P)
| or_intror (q: Q)            
.

Notation "A \/ B" := (or A B) : type_scope.

Inductive False : Type :=
.

Inductive True : Type :=
| I  
.


Check (forall P Q : Type, P /\ Q -> P).

Definition pq_imp_p (P Q : Type) (pq: P /\ Q) : P :=
  match pq with
  | conj p q => p
  end.

Check pq_imp_p.

Check ((forall P Q, P -> P /\ Q) -> False).

Definition p_imp_pq_absurd (f: forall P Q, P -> P /\ Q) : False :=
  match (@f True False (I: True)) with
  | conj p q => q
  end.

Check p_imp_pq_absurd.

(**
  Constructive Math vs. Classical Math
 **)

Definition EXM_imp_DNN (EXM: forall Q: Type, Q \/ (Q -> False))
           (P: Type) (NNP: ((P -> False) -> False)) : P
  :=
    match EXM P with
    | or_introl _ Ppf => Ppf
    | or_intror _ NPpf => match NNP NPpf with
                          end
    end.

Check EXM_imp_DNN.

(**
  Dependent Types
 **)

Inductive List (T: Type) : Type :=
| nil
| cons (hd: T) (tl: List T)
.
Arguments nil {T}.

(*
List T: the set of lists of elements of T.

VecN n: the set of lists of natural numbers of length n

List: Type -> Type
VecN: Nat -> Type
*)

Inductive VecN : nat -> Type :=
| vnil : VecN 0
| vcons (hd: nat) (n: nat) (tl: VecN n) : VecN (S n)
.

Check (vnil).
Check (vcons 3 (vcons 2 vnil)).
Check (vcons 1 (vcons 2 (vcons 3 vnil))).

  (* List Nat -> Nat *)    (* forall _:List Nat, Nat *)

  (*  (n:nat) -> VecN n *) (* forall n: nat, VecN n *)
  (*  nat -> List nat *)                                   


Inductive eq: forall A: Type, A -> A -> Type :=
| eq_refl A (x: A) : eq x x
.

Notation "x = y" := (eq x y) (at level 70) : type_scope.

Check (eq_refl (cons 3 nil)).

(*
Fixpoint plus (x y: nat) : nat :=
  match x with
  | 0 => y
  | S x0 => S (plus x0 y)         
  end.
 *)

Fixpoint proof_of_false (n:nat) : nat :=
  match n with
  | 0 => 0  
  | S n0 => proof_of_false n0
  end.

(*
x^0 + x^1 + x^2 + ...  : [0,1] -> [0,1]

nat -> A

eq_refl 2 : 2 = 2
eq_refl (1+1) : 1+1 = 1+1

eq_refl 2 : 2 = 2
*)

Definition eq_rec_r: forall (A : Type) (x : A) (y : A) (EQ: x = y) (P : A -> Type), P y -> P x :=
  fun A x y EQ => match EQ with
                  | eq_refl z => (fun P PF => PF)
                  end.

Print eq_rec_r.

Fixpoint nat_rec_r (P: nat -> Type) (BASE: P 0) (IND: forall m, P m -> P (S m)) (n: nat) : P n :=
  match n with
  | 0 => BASE
  | S m => IND m (nat_rec_r P BASE IND m)
  end.

Fixpoint foo (n: nat) : 1+n = n+1 :=
  match n with
  | 0 => eq_refl 1
  | S n0 => eq_rec_r (foo n0) (fun z => S z = S _) (eq_refl _)
  end.           

Check (forall n: nat, 1 + n = n + 1).

Definition eq_x_plus_Sy: forall x y, x + S y = S (x + y) :=
  fun x y =>
  nat_rec_r (fun x => x + S y = S (x + y))
            (eq_refl _)
            (fun x0 PF => eq_rec_r PF (fun z => S z = _) (eq_refl _))
            x.

(*
  Existential Quantification
*)

Inductive ex (A : Type) (P : A -> Type) : Type :=
| ex_intro (a : A) (pf: P a) : ex P
.

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists' '/ ' x .. y , '/ ' p ']'")
                                  : type_scope.

Definition even_exists: forall n, exists m, m = n + n :=
  fun n => ex_intro _ (n+n) (eq_refl (n+n)).

Definition case_nat: forall n, n = 0 \/ exists m, n = S m :=
  fun n =>
  match n with
  | 0 => or_introl _ (eq_refl 0)
  | S n0 => or_intror _ (ex_intro _ n0 (eq_refl (S n0)))
  end.


(*
Choice (exists f: nat -> nat, P f) : nat->nat
forall f g: nat -> nat, P f -> P g -> forall n, f n = g n.
 *)

