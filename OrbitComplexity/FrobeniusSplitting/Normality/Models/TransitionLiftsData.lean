import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Basic

/-! # Transition coefficients lifted through injective coordinate maps -/

open CategoryTheory
noncomputable section
universe u v
namespace FrobeniusSplitting

/-- Lifted units and translations retain their values, scalar cocycles and all restrictions. -/
def transitionLiftSpec {I : Type v} {R K : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s) : Prop :=
  let C := {s : Finset I // s.Nonempty}
  ∃ (c₀ : ∀ (s : C) (j : I) (_ : j ∈ s.val) (k : I) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a₀ : ∀ (s : C) (j : I) (_ : j ∈ s.val) (k : I) (_ : k ∈ s.val), N.obj s),
    (∀ s j hj k hk, (e.app s).hom (c₀ s j hj k hk : N.obj s) = (c s j hj k hk : F.obj s)) ∧
    (∀ s j hj k hk, (e.app s).hom (a₀ s j hj k hk) = a s j hj k hk) ∧
    (∀ s j hj k hk l hl,
      c₀ s j hj l hl = c₀ s k hk l hl * c₀ s j hj k hk ∧
      a₀ s j hj l hl = (c₀ s k hk l hl : N.obj s) * a₀ s j hj k hk + a₀ s k hk l hl) ∧
    ∀ (s t : C) (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toRingHom.toMonoidHom (c₀ s j hj k hk) =
        c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (N.map f).hom (a₀ s j hj k hk) =
        a₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)

end FrobeniusSplitting
