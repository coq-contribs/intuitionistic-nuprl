Notation "T # U" := (T * U)%type (at level 80, right associativity).

Inductive W (A : Type) (B : A -> Type) : Type :=
| sup :  forall (a : A) ( b: B a -> W A B ), W A B.

Definition WI'
           (I : Type)
           (A : I -> Type)
           (B : forall (i : I), A i -> Type)
           (C : forall (i : I) (a : A i), B i a -> I) :=
  W {i : I & A i}
    (fun p =>
       match p with
         | existT i a => B i a
       end).

Definition matching_indices
           {I A B C}
           (i : I)
           (a : A i)
           (p : I # B i a)
           (f : (I # B i a) -> WI' I A B C) :=
  match f p with
    | sup (existT i' _) _ => fst p = i'
  end.

Fixpoint correct_indices {I A B}
         (C : forall (i : I) (a : A i), B i a -> I)
         (w : WI' I A B C)
         (j : I) : Type :=
  match w with
    | sup (existT i a) f =>
      i = j
      # forall (b : B i a), correct_indices C (f b) (C i a b)
  end.

Definition WI I A B C i := {w : WI' I A B C & correct_indices C w i}.

Lemma corr {I A B C} :
  forall (i : I) (a : A i) (f : forall (b : B i a), WI I A B C (C i a b)),
    correct_indices
      C
      (sup
         {i : I & A i}
         (fun p =>
            match p with
              | existT i a => B i a
            end)
         (existT (fun i => A i) i a)
         (fun b => projT1 (f b)))
      i .
Proof.
  intros i a f.
  simpl; split; auto.
  intros b.
  destruct (f b); simpl; auto.
Qed.

Definition supi {I A B C}
           (i : I)
           (a : A i)
           (f : forall b : B i a, WI I A B C (C i a b)) :=
  existT (fun w : WI' I A B C => correct_indices C w i)
         (sup
            {i : I & A i}
            (fun p =>
               match p with
                 | existT i a => B i a
               end)
            (existT (fun i => A i) i a)
            (fun b => projT1 (f b)))
         (corr i a f).

Definition exWIC {A B} :=
  fun n (a : A n) (b : B n a) =>
    match n with
      | 0 => 0
      | S m => m
    end.

Inductive void : Type := .

Definition exWI :=
  WI nat
     (fun n =>
        match n with
          | 0 => unit
          | _ => nat
        end)
     (fun n a =>
        match n with
          | 0 => void
          | S m => unit
        end)
     exWIC.

Definition ex_nil : exWI 0 :=
  supi 0 tt (fun (b : void) => match b with end).

Definition ex_one : exWI 1 :=
  supi 1 22 (fun (b : unit) => ex_nil).

Definition ex_cons (n : nat) x (l : exWI n) : exWI (S n) :=
  supi (S n) x (fun (b : unit) => l).
