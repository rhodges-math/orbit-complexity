import OrbitComplexity.GroupActions.Rosenlicht.AffineOpenPoints

/-!
# OpenValueUnits
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

private abbrev chartCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

variable {K : Type u} [Field K] (X : GroupActions.Variety K)

/-- Evaluation of an affine section is invertible at each rational point
lying in its basic open subset. -/
theorem affineOpenPointEval_isUnit (U : X.scheme.Opens) (hU : IsAffineOpen U)
    (p : (X.openSubvariety U).points) (d : Γ(X.scheme, U))
    (hp : X.pointMap (mapPoints (X.openInclusion U) p) ∈ X.scheme.basicOpen d) :
    IsUnit (affineOpenPointEval X U hU p d) := by
  let _ : U.toScheme.Over (Spec (.of K)) := ⟨U.ι ≫ X.toSpec⟩
  have : IsAffine U.toScheme := hU
  let : Algebra K Γ(U.toScheme, ⊤) := chartCoordinateAlgebra (.of K) U.toScheme
  let p' : Spec (.of K) ⟶ U.toScheme := p.val
  have hp' : U.ι (p' (IsLocalRing.closedPoint K)) ∈ X.scheme.basicOpen d := hp
  rw [← U.ι_image_basicOpen_topIso_inv d] at hp'
  change U.ι (p' (IsLocalRing.closedPoint K)) ∈
    U.ι '' (U.toScheme.basicOpen (U.topIso.inv d) : Set U.toScheme) at hp'
  obtain ⟨z, hz, he⟩ := hp'
  have hmem : p' (IsLocalRing.closedPoint K) ∈
      U.toScheme.basicOpen (U.topIso.inv d) := by
    have hzi := (Scheme.Hom.isOpenEmbedding U.ι).injective he
    exact hzi ▸ hz
  have hpre : IsLocalRing.closedPoint K ∈
      p' ⁻¹ᵁ U.toScheme.basicOpen (U.topIso.inv d) := hmem
  rw [Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine'] at hpre
  have hne : (Scheme.ΓSpecIso (.of K)).hom (p'.appTop (U.topIso.inv d)) ≠ 0 := by
    intro he
    change (Scheme.ΓSpecIso (.of K)).hom (p'.appTop (U.topIso.inv d)) ∉
      (IsLocalRing.closedPoint K).asIdeal at hpre
    exact hpre (he ▸ (IsLocalRing.closedPoint K).asIdeal.zero_mem)
  apply isUnit_iff_ne_zero.mpr
  change ((affineSchemePointsEquiv K U.toScheme) p) (U.topIso.inv d) ≠ 0
  have heval := affineSchemePointsEquiv_apply K U.toScheme p (U.topIso.inv d)
  exact fun hz ↦ hne (heval.symm.trans hz)

end

end GroupActions.Variety
