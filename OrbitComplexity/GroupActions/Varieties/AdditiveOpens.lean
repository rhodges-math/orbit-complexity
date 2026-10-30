import OrbitComplexity.GroupActions.Varieties.CoordinateCharts
import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-! # Rational points of the punctured additive group

The canonical additive parameter evaluates the generator of the symmetric algebra.
Its nonvanishing therefore describes the rational image of the punctured additive group.
-/

open CategoryTheory AlgebraicGeometry
namespace GroupActions
noncomputable section
universe u
variable (K : Type u) [Field K]

private theorem affineBasic_mem {A : Type u} [CommRing A] [Algebra K A]
    [IsReduced A] [Algebra.FiniteType K A] (a : A) (x : (affineVariety K A).points) :
    (affineVariety K A).pointMap x ∈ PrimeSpectrum.basicOpen a ↔
      affineVarietyPointsEquiv K A x a ≠ 0 := by
  obtain ⟨p, rfl⟩ := affinePointsEquiv.surjective x
  rw [show (affineVariety K A).pointMap (affinePointsEquiv p) =
      (⟨RingHom.ker p, RingHom.ker_isPrime p⟩ : PrimeSpectrum A) from
        affinePointsEquiv_prime p]
  change p a ≠ 0 ↔ (affinePointsEquiv.symm (affinePointsEquiv p)) a ≠ 0
  rw [Equiv.symm_apply_apply]

private theorem additive_eval_generator (a : (additiveVariety K).points) :
    affineVarietyPointsEquiv K (SymmetricAlgebra K K) a (SymmetricAlgebra.ι K K 1) =
      (additivePointsEquiv K).symm a := by
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
  rw [Equiv.symm_apply_apply]
  let g := ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have ht : additivePointsEquiv K t = affinePointsEquiv g := rfl
  rw [ht]
  change (affinePointsEquiv.symm (affinePointsEquiv g)) (SymmetricAlgebra.ι K K 1) = t
  rw [Equiv.symm_apply_apply]
  dsimp only [g]
  rw [TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι]
  rfl

/-- Membership in the punctured additive open is nonvanishing of the canonical parameter. -/
theorem mem_additiveNonzero (x : (additiveVariety K).points) :
    (additiveVariety K).pointMap x ∈ additiveNonzero K ↔
      (additivePointsEquiv K).symm x ≠ 0 := by
  exact (affineBasic_mem K (SymmetricAlgebra.ι K K 1) x).trans
    (by rw [additive_eval_generator K x])

/-- The punctured additive inclusion has exactly the points with nonzero parameter. -/
theorem additiveNonzero_points [IsAlgClosed K] :
    Set.range (Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K))) =
      {x | (additivePointsEquiv K).symm x ≠ 0} := by
  rw [Variety.range_mapPoints, Variety.openInclusion_range]
  ext x
  exact mem_additiveNonzero K x

end
end GroupActions
