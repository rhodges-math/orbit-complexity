import OrbitComplexity.ReductiveGroups.Groups.Additive.GaSl2Reflection
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCharacterRoots
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupRootIntegration
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalRootEigenvectors

/-!
# Reductive Root Reflection Point

A root reflection acting on the original maximal-torus tangent is realized
by three points of the reductive affine group. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- A nonidentity occurring character of the fixed maximal torus
produces a point whose adjoint action is its rank-one reflection on
the torus tangent.  -/
theorem reductive_exists_root_reflection_point
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : Multiplicative (ι →₀ ℤ))
    (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) (hα : α ≠ 1) :
    ∃ (g : WithConv (B →ₐ[K] K)) (h : diagonalizableTangentImage π),
      characterDifferentialOnImage π hπ α h = 2 ∧
      ∀ t : diagonalizableTangentImage π,
        affineGroupAdjointRepresentation g (t : 𝔤) =
          (t : 𝔤) - characterDifferentialOnImage π hπ α t • (h : 𝔤) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let χ := (nonidentityCharacterLieWeightEquiv π hπ ⟨α, hocc, hα⟩).val
  have hχ : χ.IsNonZero :=
    (nonidentityCharacterLieWeightEquiv π hπ ⟨α, hocc, hα⟩).property
  obtain ⟨h, e, f, hs, he, hf, hh⟩ :=
    centralRadical_exists_isSl2Triple H χ hχ
  have hχ0 : (χ : H → K) ≠ 0 := hχ
  have hχneg : (-(χ : H → K)) ≠ 0 := neg_ne_zero.mpr hχ0
  let x := rootVectorGaMorphism H (χ : H → K) hχ0 e he
  let y := rootVectorGaMorphism H (-(χ : H → K)) hχneg f hf
  let g := gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
    gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
    gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))
  refine ⟨g, ⟨h, hh⟩, ?_, ?_⟩
  · rw [← nonidentityCharacterLieWeightEquiv_apply π hπ ⟨α, hocc, hα⟩]
    exact centralRadical_sl2_root_apply_eq_two H χ hχ hs he hh
  · intro t
    have hte : ⁅(t : 𝔤), e⁆ = χ t • e :=
      CentralRadical.lie_eq_smul_of_mem_rootSpace H χ hχ he t
    have htf : ⁅(t : 𝔤), f⁆ = (-χ t) • f := by
      let χneg : Weight K H 𝔤 := ⟨-(χ : H → K), by
        intro hz
        have hzero : f = 0 :=
          (LieSubmodule.eq_bot_iff (N := rootSpace H (-(χ : H → K)))).mp hz f hf
        exact hs.f_ne_zero hzero⟩
      have hχneg' : χneg.IsNonZero := by
        change (-(χ : H → K)) ≠ 0
        exact hχneg
      have htf' := CentralRadical.lie_eq_smul_of_mem_rootSpace H χneg hχneg' hf t
      change ⁅(t : 𝔤), f⁆ = (-χ t) • f at htf'
      exact htf'
    have hpoint := gaSl2PointProduct_adjoint_reflection x y h (t : 𝔤)
      (χ t) (by simpa [x, y] using hs) (by simpa [x] using hte)
      (by simpa [y] using htf)
    simpa only [g, χ, nonidentityCharacterLieWeightEquiv_apply] using hpoint

/-- The point by the rank-one construction maps the torus
tangent onto itself. This is a tangent statement, not torus normalization. -/
theorem ReductiveRootReflectionPoint.root_reflection_point_tangent_bijective
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : Multiplicative (ι →₀ ℤ))
    (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) (hα : α ≠ 1) :
    ∃ g : WithConv (B →ₐ[K] K),
      (∀ t : diagonalizableTangentImage π,
        affineGroupAdjointRepresentation g (t : 𝔤) ∈ diagonalizableTangentImage π) ∧
      (∀ t : diagonalizableTangentImage π,
        ∃ u : diagonalizableTangentImage π,
          affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤)) := by
  obtain ⟨g, h, hh, hg⟩ :=
    reductive_exists_root_reflection_point I hI π hπ hker hB α hocc hα
  let χ := characterDifferentialOnImage π hπ α
  let R : diagonalizableTangentImage π → diagonalizableTangentImage π := fun t =>
    ⟨affineGroupAdjointRepresentation g (t : 𝔤), by
      rw [hg t]
      exact (diagonalizableTangentImage π).sub_mem t.property
        ((diagonalizableTangentImage π).smul_mem _ h.property)⟩
  have hR (t : diagonalizableTangentImage π) : R t = t - χ t • h := by
    apply Subtype.ext
    exact hg t
  have hR2 (t : diagonalizableTangentImage π) : R (R t) = t := by
    rw [hR (R t), hR t]
    have hhχ : χ h = 2 := hh
    simp only [map_sub, map_smul, hhχ]
    module
  refine ⟨g, ?_, ?_⟩
  · intro t
    exact (R t).property
  · intro t
    refine ⟨R t, ?_⟩
    exact congrArg Subtype.val (hR2 t)

end ReductiveGroups
