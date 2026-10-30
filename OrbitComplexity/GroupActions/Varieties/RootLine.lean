import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints
import OrbitComplexity.GroupActions.Varieties.AdditiveVariety
import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedTangentCriterion
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Additive parameters on root lines

A nonzero additive map whose tangent lies in a closed singleton root subgroup identifies
that subgroup with the additive line. The isomorphism preserves its specified parameter.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (r : G.rootIndex) (hr : G.rootBase.IsPos r)
  (hR : IsPositiveRootClosed G.rootBase {r})
  (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
  (ht : ∀ b ∈ G.rootSubsetIdeal {r} hR, gaAffineGroupTangent φ b = 0)
  (hφ : gaAffineGroupTangent φ ≠ 0)

private theorem polynomialEndo_injective {F : Type*} [Field F]
    (f : Polynomial F →ₐ[F] Polynomial F) (hf : Function.Surjective f) :
    Function.Injective f := by
  have he (p : Polynomial F) : f p = p.comp (f Polynomial.X) := by
    have h : f = Polynomial.aeval (f Polynomial.X) := Polynomial.algHom_ext (by simp)
    exact DFunLike.congr_fun h p
  obtain ⟨p, hp⟩ := hf Polynomial.X
  have hdeg : (f Polynomial.X).natDegree ≠ 0 := by
    intro h
    have hd := congrArg Polynomial.natDegree hp
    rw [he, Polynomial.natDegree_comp, h, mul_zero, Polynomial.natDegree_X] at hd
    exact Nat.zero_ne_one hd
  intro a b hab
  have hz : (a - b).comp (f Polynomial.X) = 0 := by
    rw [← he, map_sub, hab, sub_self]
  rcases Polynomial.comp_eq_zero_iff.mp hz with hz | hz
  · exact sub_eq_zero.mp hz
  · apply (hdeg ?_).elim
    rw [hz.2, Polynomial.natDegree_C]

@[instance_reducible] private def rootLineUnique :
    Unique {s : G.rootIndex // G.rootBase.IsPos s ∧ s ∈ ({r} : Set _)} where
  default := ⟨r, hr, Set.mem_singleton r⟩
  uniq s := Subtype.ext (Set.mem_singleton_iff.mp s.property.2)

private def rootLinePolynomial : G.rootSubsetAlgebra {r} hR ≃ₐ[K] Polynomial K := by
  letI := rootLineUnique G r hr
  exact (G.rootSubsetCoordinateEquiv {r} hR).trans (MvPolynomial.uniqueAlgEquiv K _)

private def rootLinePullback : G.rootSubsetAlgebra {r} hR →ₐ[K] SymmetricAlgebra K K :=
  Ideal.Quotient.liftₐ (G.rootSubsetIdeal {r} hR).toIdeal φ.toAlgHom
    ((gaMorphism_kills_hopfIdeal_iff φ _).mpr ht)

include hφ in
private theorem rootLinePullback_surjective :
    Function.Surjective (rootLinePullback G r hR φ ht) := by
  intro b
  obtain ⟨a, ha⟩ := gaMorphism_surjective_of_tangent_ne_zero φ hφ b
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- The specified additive parameter is an isomorphism on root-line coordinate algebras. -/
def rootLineCoordinateEquiv : G.rootSubsetAlgebra {r} hR ≃ₐ[K] SymmetricAlgebra K K := by
  let f := rootLinePullback G r hR φ ht
  have hf : Function.Surjective f := rootLinePullback_surjective G r hR φ ht hφ
  let a := rootLinePolynomial G r hr hR
  let b := gaPolynomialEquiv K
  let ψ : Polynomial K →ₐ[K] Polynomial K := b.toAlgHom.comp (f.comp a.symm.toAlgHom)
  have hψ : Function.Injective ψ := polynomialEndo_injective ψ
    (b.surjective.comp (hf.comp a.symm.surjective))
  apply AlgEquiv.ofBijective f
  refine ⟨?_, hf⟩
  intro x y hxy
  apply a.injective
  apply hψ
  change b (f (a.symm (a x))) = b (f (a.symm (a y)))
  simpa only [AlgEquiv.symm_apply_apply] using congrArg b hxy

/-- A nonzero additive root parameter identifies its closed root line with the additive variety. -/
def rootLineIso : (additiveVariety K).toOver ≅ (rootSubsetVariety G {r} hR).toOver :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (rootLineCoordinateEquiv G r hr hR φ ht hφ)).op

/-- The root-line isomorphism composes to the specified additive morphism in the group. -/
theorem rootLineIso_hom_comp :
    (rootLineIso G r hr hR φ ht hφ).hom ≫ rootSubsetInclusion G {r} hR = gaMorphism G φ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (rootLineCoordinateEquiv G r hr hR φ ht hφ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (G.rootSubsetIdeal {r} hR).toIdeal)) = _
  rw [← Spec.map_comp]
  congr 1

/-- The root-line isomorphism preserves the specified field-valued additive parameter. -/
theorem rootLineIso_points (t : K) :
    (rootSubsetPointsMulEquiv G {r} hR
      (Variety.mapPoints (rootLineIso G r hr hR φ ht hφ).hom
        (additivePointsEquiv K t)) : G.points) = gaParameterPoint φ t := by
  apply (reductivePointsEquiv G).injective
  rw [← rootSubsetInclusion_points, ← Variety.mapPoints_comp, rootLineIso_hom_comp]
  exact gaMorphism_points G φ t
end
end GroupActions
