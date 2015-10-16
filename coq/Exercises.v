Require Import Category.

(** * Exercise 5 1 *)
Module Ex_5_1.
  Context (cat : Category).
  Context (A B C one : ob).

  (** ** a *)
  Theorem a : forall `(f : A ⟶ B) `(h : A ⟶ C),
      (exists g : B ⟶ C, h = g ∘ f) -> (forall a1 a2 : one ⟶ A, f ∘ a1 = f ∘ a2 -> h ∘ a1 = h ∘ a2).
  Proof.
    intros f h Hexg a1 a2 Hf.
    inversion_clear Hexg as [g Hg].
    rewrite Hg.
    repeat rewrite <- assoc.
    rewrite Hf.
    reflexivity.
  Qed.

  (** ** b *)
  Theorem b : forall `(f : A ⟶ B) `(h : A ⟶ C),
      (forall a1 a2 : one ⟶ A, f ∘ a1 = f ∘ a2 -> h ∘ a1 = h ∘ a2) -> (exists g : B ⟶ C, h = g ∘ f).
  Proof.
    intros f h Has.
  Admitted.

End Ex_5_1.
(** [] *)

(** * Exercise 5 2 *)
Module Ex_5_2.
  Context (cat : Category).
  Context (A B C one : ob).

  (** ** a *)
  Theorem a : forall (g : B ⟶ C) (h : A ⟶ C),
      (exists f : A ⟶ B, g ∘ f = h) -> (forall a : one ⟶ A, exists b : one ⟶ B, h ∘ a = g ∘ b).
  Proof.
    intros g h Hexf a.
    inversion_clear Hexf as [f Hf].
    exists (f ∘ a).
    rewrite assoc.
    rewrite Hf.
    reflexivity.
  Qed.

  (** ** b *)
  Section b.
    Hypothesis choice : forall (A B : ob), forall (R : one ⟶ A -> one ⟶ B -> Prop),
        (forall a : one ⟶ A, exists b : one ⟶ B, R a b) ->
        (exists f : A ⟶ B, forall a : one ⟶ A, R a (f ∘ a)).
    Hypothesis extensionality : forall (A B : ob) (f g : A ⟶ B),
        (forall a : one ⟶ A, f ∘ a = g ∘ a) -> f = g.
    Theorem b : forall (g : B ⟶ C) (h : A ⟶ C),
        (forall a : one ⟶ A, exists b : one ⟶ B, h ∘ a = g ∘ b) -> (exists f : A ⟶ B, g ∘ f = h).
    Proof.
      intros g h Ha.
      specialize (choice A).
      specialize (choice B).
      specialize (choice (fun a b => h ∘ a = g ∘ b)).
      apply choice in Ha.
      clear choice.
      inversion_clear Ha as [f Hf].
      exists f.
      apply extensionality.
      intros a.
      symmetry.
      rewrite <- assoc.
      apply Hf.
    Qed.
  End b.
End Ex_5_2.

(** * Stacking in a Chinese Restaurant *)
Instance Category_Type : Category :=
  {ob := Type;
   mp := fun A B => A -> B;
   id := fun A => fun x => x;
   comp := fun A B C => fun f g => fun x => g (f x)}.
- intros A B g. reflexivity.
- intros A B f. reflexivity.
- intros A B f C g D h. reflexivity.
Defined.

Module StackingInAChineseRestaurant.
  Section StackingInAChineseRestaurant.

    Inductive KindsOfItems : Set :=
    | MooShuPork
    | SteamedRice
    | Tea.

    Definition AmountsOfMoney := nat.

    Definition price : KindsOfItems -> AmountsOfMoney :=
      fun k =>
        match k with
        | MooShuPork => 5
        | SteamedRice => 2
        | Tea => 1%nat
        end.

    Inductive ItemsConsumedAtTheTable : Set :=
    | item1
    | item2
    | item3
    | item4
    | item5.

    Definition kind : ItemsConsumedAtTheTable -> KindsOfItems :=
      fun i =>
        match i with
        | item1 => Tea
        | item2 => SteamedRice
        | item3 => MooShuPork
        | item4 => SteamedRice
        | item5 => Tea
        end.

    Require Import Arith.
    Require Import List.
    Import ListNotations.

    Theorem eq_dec_KindsOfItems : forall (x y : KindsOfItems),
        {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct x; destruct y;
      try (left; reflexivity);
      right; intros contra; inversion contra.
    Defined.

    Definition price_k : AmountsOfMoney :=
      let sizeOfStack k :=
          count_occ eq_dec_KindsOfItems
                    (map kind [item1; item2; item3; item4; item5]) k in
      let product k := sizeOfStack k * price k in
      product MooShuPork + product SteamedRice + product Tea.

    Compute price_k.

    Definition f : ItemsConsumedAtTheTable -> AmountsOfMoney :=
      price ∘ kind.

    Definition price_x : AmountsOfMoney :=
      let sizeOfStack x :=
          count_occ eq_nat_dec
                    (map f [item1; item2; item3; item4; item5]) x in
      let product x := sizeOfStack x * x in
      product 5 + product 2 + product (1%nat).

    Compute price_x.

    Inductive ShapesOfPlates : Set :=
    | Triangle
    | Square
    | Circle.

    Definition shape : KindsOfItems -> ShapesOfPlates :=
      fun k =>
        match k with
        | MooShuPork => Triangle
        | SteamedRice => Square
        | Tea => Circle
        end.

    Definition shape_retraction : ShapesOfPlates -> KindsOfItems :=
      fun s =>
        match s with
        | Triangle => MooShuPork
        | Square => SteamedRice
        | Circle => Tea
        end.

    Require Import FunctionalExtensionality.

    Theorem shape_has_retraction : Retraction shape shape_retraction.
    Proof.
      apply functional_extensionality.
      intros x.
      destruct x; reflexivity.
    Qed.

    Definition price' : ShapesOfPlates -> AmountsOfMoney :=
      price ∘ shape_retraction.

    Theorem price_price'_shape : price = price' ∘ shape.
    Proof.
      apply functional_extensionality.
      intros x.
      destruct x; reflexivity.
    Qed.

    Inductive EmptyPlatesLeftOnTable : Set :=
    | plate1
    | plate2
    | plate3
    | plate4
    | plate5.

    Definition kind' : EmptyPlatesLeftOnTable -> ShapesOfPlates :=
      fun p =>
        match p with
        | plate1 => Circle
        | plate2 => Square
        | plate3 => Triangle
        | plate4 => Square
        | plate5 => Circle
        end.

    Definition f' : EmptyPlatesLeftOnTable -> AmountsOfMoney :=
      price' ∘ kind'.

    Theorem eq_dec_ShapesOfPlates : forall (x y : ShapesOfPlates),
        {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct x; destruct y;
      try (left; reflexivity);
      right; intros contra; inversion contra.
    Defined.

    Definition price_s : AmountsOfMoney :=
      let sizeOfStack s :=
          count_occ eq_dec_ShapesOfPlates
                    (map kind' [plate1; plate2; plate3; plate4; plate5]) s in
      let product s := price' s * sizeOfStack s in
      product Triangle + product Square + product Circle.

    Compute price_s.

    Definition price_x' : AmountsOfMoney :=
      let sizeOfStack x :=
          count_occ eq_nat_dec
                    (map f' [plate1; plate2; plate3; plate4; plate5]) x in
      let product x := sizeOfStack x * x in
      product 5 + product 2 + product (1%nat).

    Compute price_x'.

    Definition dining : ItemsConsumedAtTheTable -> EmptyPlatesLeftOnTable :=
      fun i =>
        match i with
        | item1 => plate1
        | item2 => plate2
        | item3 => plate3
        | item4 => plate4
        | item5 => plate5
        end.

    Theorem shape_kind_kind'_dining : shape ∘ kind = kind' ∘ dining.
    Proof.
      apply functional_extensionality.
      intros x.
      destruct x; reflexivity.
    Qed.

    Theorem f_f'_dining : f = f' ∘ dining.
    Proof.
      unfold f, f'.
      rewrite price_price'_shape.
      repeat rewrite <- (@assoc Category_Type).
      rewrite <- shape_kind_kind'_dining.
      reflexivity.
    Qed.

    Theorem dining_is_isomorphism : Isomorphism dining.
    Proof.
      unfold Isomorphism.
      exists (fun p =>
           match p with
           | plate1 => item1
           | plate2 => item2
           | plate3 => item3
           | plate4 => item4
           | plate5 => item5
           end).
      unfold Inverse.
      split;
        (apply functional_extensionality;
         intros x;
         destruct x;
         reflexivity).
    Qed.

  End StackingInAChineseRestaurant.
End StackingInAChineseRestaurant.
