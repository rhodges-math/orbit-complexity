import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionVariety
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionGroups
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionRadical
import OrbitComplexity.SchubertGeometry.Levi.Reductive

/-! # Standard parabolic and Levi structure

The parabolic Bruhat union, reductive Levi and its Borel, and the unipotent radical
agree with multiplication and the internal semidirect decomposition.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The standard parabolic has its Bruhat union, Levi product and unipotent radical. -/
theorem parabolic_structure (I : Set G.rootBase.support) :
    (∀ v : G.weylGroup, v ∈ standardParabolicSubgroup G.rootBase I ↔
      ∃ l : List G.rootBase.support, (∀ i ∈ l, i ∈ I) ∧
        simpleWeylWord G.rootBase l = v) ∧
    (((standardParabolicPoints G I : Set G.points) =
      ⋃ v : G.weylGroup, ⋃ (_ : v ∈ standardParabolicSubgroup G.rootBase I),
        subgroupDoubleCoset G.borelPoints (G.weylPoint v)) ∧
      IsClosed (standardParabolicPoints G I : Set G.points)) ∧
    IsClosedImmersion (standardParabolicInclusion G I).left ∧
    IsMonHom (standardParabolicInclusion G I) ∧
    reductiveCommHopfAlgProperty K (G.leviAlgebra I) ∧
    G.leviBorelPoints I = G.leviPoints I ⊓ G.borelPoints ∧
    HopfIdeal.IsBorel K (G.leviAlgebra I).obj (leviBorelIdealInLevi G I) ∧
    (unipotentInParabolic G I).Normal ∧
    (leviInParabolic G I).IsComplement' (unipotentInParabolic G I) ∧
    (∃ e : (parabolicLeviProduct G I).toOver ≅ (standardParabolicVariety G I).toOver,
      e.hom = parabolicMultiplication G I) ∧
    parabolicUnipotentIdeal G I =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (parabolicAlgebra G I) := by
  exact ⟨mem_standardParabolicSubgroup_iff_word G.rootBase I,
    standardParabolicPoints_bruhat G I, parabolicInclusion_isClosed G I,
    parabolicInclusion_isMonHom G I, levi_reductive G I, rfl,
    leviBorel_isBorel G I, parabolicUnipotent_normal G I, parabolicComplement G I,
    ⟨parabolicLeviIso G I, rfl⟩, parabolicUnipotent_isRadical G I⟩

end
end SchubertGeometry
