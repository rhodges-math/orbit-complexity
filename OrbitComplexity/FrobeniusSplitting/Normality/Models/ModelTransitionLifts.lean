import OrbitComplexity.FrobeniusSplitting.Normality.Models.TransitionLifts
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ScalarImageBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams

/-! # Transition parameters in the specified enlarged model -/

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- Generic evaluation is natural on every arrow of a chosen coordinate model. -/
def modelEvaluation {C : Type v} [Category.{w} C]
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (N : C ⥤ CommAlgCat.{u} R) (F : C ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom) :
    N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat where
  app s := CommRingCat.ofHom
    ((e s).toAlgHom.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  naturality {s t} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact AlgHom.congr_fun (he s t f) ((1 : K) ⊗ₜ[R] x)

/-- Base change of the same prior diagram retains its units, inverses and translations. -/
theorem retained_transition_lifts {I : Type v}
    {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K]
    (P : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (hi : ∀ s, Function.Injective (fun x : N.obj s ↦ e s ((1 : K) ⊗ₜ[R] x)))
    (q : fixedFibreDiagram (R := R) (M := R) P ≅ N)
    (v : ∀ s, P.obj s →+* F.obj s)
    (hq : ∀ s x, e s ((1 : K) ⊗ₜ[R] (q.hom.app s).hom ((1 : R) ⊗ₜ[S] x)) = v s x)
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (hm : ∀ s j hj k hk,
      (c s j hj k hk : F.obj s) ∈ Set.range (v s) ∧
      (↑((c s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (v s) ∧
      a s j hj k hk ∈ Set.range (v s))
    (hco : ∀ s j hj k hk l hl,
      c s j hj l hl = c s k hk l hl * c s j hj k hk ∧
      a s j hj l hl = (c s k hk l hl : F.obj s) * a s j hj k hk + a s k hk l hl)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (F.map f).hom (a s j hj k hk) =
        a t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    transitionLiftSpec N F (modelEvaluation N F e he) c a := by
  apply exists_transition_lifts N F (modelEvaluation N F e he) hi c a ?_ hco hn
  intro s j hj k hk
  have hmem (z : F.obj s) (hz : z ∈ Set.range (v s)) :
      z ∈ Set.range ((modelEvaluation N F e he).app s).hom := by
    obtain ⟨x, hx⟩ := hz
    exact ⟨(q.hom.app s).hom ((1 : R) ⊗ₜ[S] x), (hq s x).trans hx⟩
  exact ⟨hmem _ (hm s j hj k hk).1, hmem _ (hm s j hj k hk).2.1,
    hmem _ (hm s j hj k hk).2.2⟩

end FrobeniusSplitting
