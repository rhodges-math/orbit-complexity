import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorModelCover
import Mathlib.RingTheory.Finiteness.Basic

/-! # A common finite coefficient extension for the prior-model cover -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v
namespace FrobeniusSplitting

/-- Finite generic patches cover the same prior model after one finite coefficient
extension and every subsequent coefficient extension. -/
theorem exists_prior_coefficient_cover {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I] {Y YK : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (X XK : I → Scheme.{u}) (f : ∀ i, X i ⟶ Y) (fK : ∀ i, XK i ⟶ YK)
    (base : Y ⟶ Spec (.of S))
    [∀ i, LocallyOfFinitePresentation (f i)] [∀ i, QuasiCompact (f i)]
    [LocallyOfFinitePresentation base] [QuasiCompact base]
    (qX : ∀ i, XK i ⟶ X i) (qY : YK ⟶ Y) (baseK : YK ⟶ Spec (.of K))
    (hsq : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hcomm : ∀ i, qX i ≫ f i = fK i ≫ qY)
    (hcoverK : ∀ y : YK, ∃ i x, fK i x = y) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      R.FG ∧ ∀ (T : Type u) [CommRing T] [Algebra R T],
        letI : Algebra S T := ((algebraMap R T).comp (algebraMap S R)).toAlgebra
        ∀ y : (pullback base (Spec.map (CommRingCat.ofHom (algebraMap S T))) : Scheme.{u}),
          ∃ i, ∃ z : (pullback (f i) (pullback.fst base
              (Spec.map (CommRingCat.ofHom (algebraMap S T)))) : Scheme.{u}),
            (pullback.snd (f i) (pullback.fst base
              (Spec.map (CommRingCat.ofHom (algebraMap S T))))) z = y := by
  obtain ⟨r, hr, hcover⟩ := exists_prior_cover_denominator
    (FaithfulSMul.algebraMap_injective S K) X XK f fK base qX qY baseK hsq hcomm hcoverK
  let A : Set K := {(algebraMap S K r)⁻¹}
  let R : Subalgebra ℤ K := S ⊔ Algebra.adjoin ℤ A
  have hSR : S ≤ R := le_sup_left
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have hR : R.FG := hS.sup (Subalgebra.fg_def.mpr ⟨A, Set.finite_singleton _, rfl⟩)
  let z : R := ⟨(algebraMap S K r)⁻¹,
    (le_sup_right : Algebra.adjoin ℤ A ≤ R) (Algebra.subset_adjoin (Set.mem_singleton _))⟩
  have hne : algebraMap S K r ≠ 0 := by
    intro h
    exact hr ((FaithfulSMul.algebraMap_injective S K) (h.trans (map_zero _).symm))
  have hu : IsUnit (algebraMap S R r) := by
    refine ⟨⟨algebraMap S R r, z, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hne
    · apply Subtype.ext
      exact inv_mul_cancel₀ hne
  refine ⟨R, hSR, hR, ?_⟩
  intro T _ _
  let : Algebra S T := ((algebraMap R T).comp (algebraMap S R)).toAlgebra
  exact hcover T (hu.map (algebraMap R T))

end FrobeniusSplitting
