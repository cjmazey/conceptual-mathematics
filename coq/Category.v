Generalizable All Variables.

Reserved Notation " A ⟶ B " (at level 70).
Reserved Notation " g ∘ f " (at level 40, left associativity).

Class Category  :=
 {ob : Type;
  mp : ob -> ob -> Type
  where " A ⟶ B " := (mp A B);
  id : `{A ⟶ A}
  where " 1 " := id;
  comp : `{A ⟶ B -> B ⟶ C -> A ⟶ C}
  where " g ∘ f " := (comp f g);
  rid : forall `(g : A ⟶ B), g ∘ 1 = g;
  lid : forall `(f : A ⟶ B), 1 ∘ f = f;
  assoc :
   forall `(f : A ⟶ B) `(g : B ⟶ C) `(h : C ⟶ D), h ∘ (g ∘ f) = h ∘ g ∘ f}.

Notation " A ⟶ B " := (@mp _ A B) : category_scope.
Close Scope nat_scope.
Notation " 1 " := (@id _ _) : category_scope.
Open Scope nat_scope.
Notation " g ∘ f " := (@comp _ _ _ _ f g) : category_scope.
Open Scope category_scope.

Section cat_definitions.

  Context  {cat : Category}.

  Definition Inverse `(f : A ⟶ B) (g : B ⟶ A) : Prop :=
    g ∘ f = 1 /\ f ∘ g = 1.

  Definition Isomorphism `(f : A ⟶ B) : Prop := exists g : B ⟶ A, Inverse f g.

  Definition Isomorphic (A B : ob) : Prop := exists f : A ⟶ B, Isomorphism f.

  Definition Epimorphism `(f : A ⟶ B) : Prop :=
    forall T (g h : B ⟶ T), g ∘ f = h ∘ f -> g = h.

  Definition Monomorphism `(f : A ⟶ B) : Prop :=
    forall T (g h : T ⟶ A), f ∘ g = f ∘ h -> g = h.

  Definition Section `(f : A ⟶ B) (s : B ⟶ A) : Prop := f ∘ s = 1.

  Definition Retraction `(f : A ⟶ B) (r : B ⟶ A) : Prop := r ∘ f = 1.

  Definition Idempotent `(e : A ⟶ A) : Prop := e ∘ e = e.

  Definition Automorphism `(e : A ⟶ A) : Prop := Isomorphism e.

End cat_definitions.

Section cat_theorems.

  Context  {cat : Category}.

  Theorem Isomorphism_1 : `(Isomorphism (1:A ⟶ A)).
  Proof.
    unfold Isomorphism.
    intros A.
    exists 1. split. apply rid. apply lid.
  Qed.

  Theorem Isomorphic_refl : `(Isomorphic A A).
  Proof.
    unfold Isomorphic.
    intros A.
    exists 1. apply Isomorphism_1.
  Qed.

  Theorem Isomorphic_sym : `(Isomorphic A B -> Isomorphic B A).
  Proof.
    unfold Isomorphic, Isomorphism.
    intros A B H.
    inversion_clear H as (f, H').
    inversion_clear H' as (g, H).
    inversion_clear H as (H1, H2).
    exists g. exists f. split; assumption.
  Qed.

  Theorem Isomorphic_trans :
   `(Isomorphic A B -> Isomorphic B C -> Isomorphic A C).
  Proof.
    unfold Isomorphic, Isomorphism.
    intros A B C Hf Hg.
    inversion_clear Hf as (f, Hf').
    inversion_clear Hf' as (f', Hf).
    inversion_clear Hf as (Hf1, Hf2).
    inversion_clear Hg as (g, Hg').
    inversion_clear Hg' as (g', Hg).
    inversion_clear Hg as (Hg1, Hg2).
    exists (g ∘ f). exists (f' ∘ g').
    split.
    replace (f' ∘ g' ∘ (g ∘ f)) with (f' ∘ (g' ∘ g) ∘ f) .
    rewrite Hg1. rewrite rid. assumption.
    rewrite !assoc. reflexivity.
    replace (g ∘ f ∘ (f' ∘ g')) with (g ∘ (f ∘ f') ∘ g') .
    rewrite Hf2. rewrite rid. assumption.
    rewrite !assoc. reflexivity.
  Qed.

  Theorem Inverse_unicity :
   forall `(f : A ⟶ B), `(Inverse f g -> Inverse f h -> g = h).
  Proof.
    unfold Inverse.
    intros A B f g h Hg Hh.
    inversion_clear Hg as (Hg1, Hg2).
    inversion_clear Hh as (Hh1, Hh2).
    rewrite <- rid.
    rewrite <- Hg2.
    rewrite assoc.
    rewrite Hh1.
    rewrite lid.
    reflexivity.
  Qed.

  Theorem Determination :
   forall `(f : A ⟶ B) `(h : A ⟶ C),
   (exists r, Retraction f r) -> exists g, g ∘ f = h.
  Proof.
    unfold Retraction.
    intros A B f C h Hret.
    inversion_clear Hret as (r, Hr).
    exists (h ∘ r). rewrite <- assoc. rewrite Hr. apply rid.
  Qed.

  Theorem Choice :
   forall `(f : B ⟶ C) `(h : A ⟶ C),
   (exists s, Section f s) -> exists g, f ∘ g = h.
  Proof.
    intros B C f A h Hsec.
    inversion_clear Hsec as (s, Hs).
    exists (s ∘ h). rewrite assoc. rewrite Hs. apply lid.
  Qed.

End cat_theorems.
