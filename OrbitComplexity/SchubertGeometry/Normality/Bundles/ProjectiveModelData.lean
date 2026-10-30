import OrbitComplexity.FrobeniusSplitting.Normality.Models.ModelTransitionLifts
import OrbitComplexity.SchubertGeometry.Normality.Transitions.TransitionData

/-! # Specified model parameters and their projective-line diagram -/

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u
namespace SchubertGeometry

/-- The same model coordinates retain all parameter values and the projective diagram. -/
def modelProjectiveSpec {I R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s) : Prop :=
  let C := {s : Finset I // s.Nonempty}
  ∃ (c₀ : ∀ (s : C) (j : I) (_ : j ∈ s.val) (k : I) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a₀ : ∀ (s : C) (j : I) (_ : j ∈ s.val) (k : I) (_ : k ∈ s.val), N.obj s),
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] (c₀ s j hj k hk : N.obj s)) = (c s j hj k hk : F.obj s)) ∧
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] a₀ s j hj k hk) = a s j hj k hk) ∧
    (∀ s j hj k hk l hl,
      c₀ s j hj l hl = c₀ s k hk l hl * c₀ s j hj k hk ∧
      a₀ s j hj l hl = (c₀ s k hk l hl : N.obj s) * a₀ s j hj k hk + a₀ s k hk l hl) ∧
    (∀ (s t : C) (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toRingHom.toMonoidHom (c₀ s j hj k hk) =
        c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (N.map f).hom (a₀ s j hj k hk) = a₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
    projectiveTransitionSpec N sel c₀ a₀

end SchubertGeometry
