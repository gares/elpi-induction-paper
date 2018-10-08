(*
Goal True.
Proof.
idtac.
idtac.
Qed.
*)

From elpi Require Import derive.

Elpi derive nat.
Elpi derive list.

Notation is_nat := nat.param1.nat.
Notation is_list := list.param1.list.

Inductive rtree A : Type :=
  Leaf (n : A) | Node (l : list (rtree A)).

Definition xxx : forall A (HA : forall a b : A, { a = b } + { ~(a = b) }) (x y : rtree A),
  { x = y } + { ~ (x = y) }.
intros A HA.
fix rec 1.
repeat decide equality.
Defined.

Print xxx.




Check rtree_ind.
(* forall (A : Type) (P : rtree A -> Prop),
       (forall n : A, P (Leaf A n)) ->
       (forall l : list (rtree A), P (Node A l)) ->
       forall r : rtree A, P r *)

Elpi derive rtree.
Notation is_rtree := rtree.param1.rtree.

Check rtree.eq.
(* forall A : Type,
     (A -> A -> bool) -> rtree A -> rtree A -> bool *)
Check rtree.eq.OK. 
(* forall (A : Type) (fa : A -> A -> bool)
         (s1 : rtree A),
       rtree.param1.rtree A (axiom A fa) s1 ->
       axiom (rtree A) (rtree.eq A fa) s1 *)
Print axiom.
(* fun (T : Type) (eqb : T -> T -> bool) (x : T) =>
     forall y : T, reflect (x = y) (eqb x y) *)
Check nat.eq.OK. 
(* forall s1 : nat, axiom nat nat.eq s1 *)

Print nat.param1.nat.
(* Inductive nat : nat -> Type :=
    O : nat.param1.nat 0
  | S : forall H : nat,
        nat.param1.nat H -> nat.param1.nat (S H) *)

Print list.param1.list.
(* Inductive list (A : Type) (PA : A -> Type) : list A -> Type :=
    nil : list.param1.list A PA nil
  | cons : forall H : A,
           PA H ->
           forall H0 : list A,
           list.param1.list A PA H0 ->
	   list.param1.list A PA (H :: H0) *)

Check list.induction.principle.
(* forall (A : Type) (PA : A -> Type)
         (P : list A -> Type),
       P nil ->
       (forall H : A,
        PA H ->
        forall H0 : list A, P H0 -> P (H :: H0)%list) ->
       forall s1 : list A,
       list.param1.list A PA s1 -> P s1 *)
Check list.param1.list_ind.
(* forall (A : Type) (PA : A -> Type)
         (P : forall s1 : list A,
              list.param1.list A PA s1 -> Prop),
       P nil (list.param1.nil A PA) ->
       (forall (a : A) (P_ : PA a) (l : list A)
          (P_0 : list.param1.list A PA l),
        P l P_0 ->
        P (a :: l)%list
          (list.param1.cons A PA a P_ l P_0)) ->
       forall (s1 : list A)
         (l : list.param1.list A PA s1), 
       P s1 l
*)
Check rtree.param1.rtreeP.
(* forall (A : Type) (PA : A -> Type),
       (forall x : A, PA x) ->
       forall x : rtree A, rtree.param1.rtree A PA x *)

Check rtree.map.
(* rtree.map
     : forall A1 A2 : Type,
       (A1 -> A2) -> rtree A1 -> rtree A2 *)

Check list.param1.map.
(* rtree.map
     : forall A1 A2 : Type,
       (A1 -> A2) -> rtree A1 -> rtree A2 *)

Check rtree.is.Node.
(* rtree.is.Node
     : forall A : Type, rtree A -> bool *)

Check list.injection.cons1.
(* list.injection.cons1
     : forall A : Type, A -> list A -> list A -> A *)
Check list.injection.cons2.
(* list.injection.cons2
     : forall A : Type, A -> list A -> list A -> list A *)
Print list.injection.cons1.
(* list.injection.cons1 = 
fun (A : Type) (H : A) (_ i : list A) =>
match i with
| nil => H
| (x :: _)%list => x
end *)

Check list.eq.bcongr.cons.
(* 
list.eq.bcongr.cons
     : forall (A : Type) (x y : A) (b : bool),
       reflect (x = y) b ->
       forall (x0 y0 : list A) (b0 : bool),
       reflect (x0 = y0) b0 ->
       reflect ((x :: x0)%list = (y :: y0)%list)
         (b && b0)
*)
Check rtree.eq.bcongr.Leaf.
(* rtree.eq.bcongr.Leaf
     : forall (A : Type) (x y : A) (b : bool),
       reflect (x = y) b ->
       reflect (Leaf A x = Leaf A y) b
*)
Print rtree.eq.
(* rtree.eq = 
fun (A : Type) (eqA : A -> A -> bool) =>
fix f (x1 x2 : rtree A) {struct x1} : bool :=
  match x1 with
  | Leaf _ n =>
      match x2 with
      | Leaf _ n0 => eqA n n0
      | Node _ _ => false
      end
  | Node _ l =>
      match x2 with
      | Leaf _ _ => false
      | Node _ l0 => list.eq (rtree A) f l l0
      end
  end
*)
Check rtree.eq.axiom.Node.
(*rtree.eq.axiom.Node
     : forall (A : Type) (f : A -> A -> bool)
         (x : list (rtree A)),
       axiom (list (rtree A))
         (list.eq (rtree A) (rtree.eq A f)) x ->
       forall x0 : rtree A,
       axiom_at (rtree A) (rtree.eq A f) (Node A x) x0*)
Print axiom_at.
Check rtree.param1.rtreeP.
Print rtree.param1.rtree.

Check nat.induction.principle.
Print nat.induction.


Print rtree.eq.correct.
Check fun (a : Type) (fa : a -> a -> bool) =>
rtree.induction.principle a (axiom a fa)
  (axiom (rtree a) (rtree.eq a fa))
  (fun (n : a) (Pn : axiom a fa n) =>
   rtree.eq.axiom.Leaf a fa n Pn)
  (fun (l : list (rtree a))
     (Pl : is_list (rtree a)
             (axiom (rtree a) (rtree.eq a fa)) l) =>
   rtree.eq.axiom.Node a fa l
     (list.eq.correct (rtree a) (rtree.eq a fa) l Pl)).
Check list.eq.correct.