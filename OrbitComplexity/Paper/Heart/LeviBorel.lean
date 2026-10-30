import OrbitComplexity.SchubertGeometry.Levi.BorelRadical
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionBorelGroups
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionBorelVariety
import OrbitComplexity.SchubertGeometry.Roots.Products
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Levi Borel groups and their unipotent radicals -/

noncomputable section
namespace SchubertOrbits
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The Levi Borel, its radical, regular torus product and internal semidirect product. -/
theorem leviBorel_definition (I : Set G.rootBase.support) :
    G.leviBorelPoints I = G.leviPoints I ⊓ G.borelPoints ∧
    HopfIdeal.IsBorel K (G.leviAlgebra I).obj (leviBorelIdealInLevi G I) ∧
    (G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I)).map
        (Bialgebra.Quotient.mkBialgHom (G.leviBorelIdeal I).toIdeal) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (G.leviBorelAlgebra I) ∧
    G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) =
      G.leviBorelPoints I ⊓ G.unipotentPoints ∧
    (∃ e : (leviBorelProduct G I).toOver ≅ (leviBorelVariety G I).toOver,
      e.hom = leviBorelMultiplication G I) ∧
    (∃ e : (rootsInLeviBorel G I) ⋊[
        ((rootsInLeviBorel G I).normalizerMonoidHom).comp (Subgroup.inclusion
          ((rootsInLeviBorel G I).normalizer_eq_top ▸ le_top))]
        (torusInLeviBorel G I) ≃* G.leviBorelPoints I,
      ∀ p, (e p : G.points) = (p.left : G.points) * (p.right : G.points)) ∧
    ∀ (l : List (G.rootCharacters (leviPositiveRoots G.rootBase I)))
      (_hl : l.Nodup) (_hall : ∀ i, i ∈ l),
      ∃ e : (affineSpaceVariety K (G.rootCharacters (leviPositiveRoots G.rootBase I))).toOver ≅
          (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
            (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toOver,
        (∀ a : G.rootCharacters (leviPositiveRoots G.rootBase I) → K,
          (rootSubsetPointsMulEquiv G _ _ (Variety.mapPoints e.hom
            ((affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
              (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
        (∀ f : (i : G.rootCharacters (leviPositiveRoots G.rootBase I)) →
            rootSubgroupPoints G (G.characterRootEquiv
              (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
          (l.map (fun i => (f i : G.points))).prod ∈
            G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
              (LeviRootSpan.isPositiveRootClosed G.rootBase I)) ∧
        ∀ g : G.points, g ∈ G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
            (LeviRootSpan.isPositiveRootClosed G.rootBase I) →
          ∃! f : (i : G.rootCharacters (leviPositiveRoots G.rootBase I)) →
              rootSubgroupPoints G (G.characterRootEquiv
                (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
            (l.map (fun i => (f i : G.points))).prod = g := by
  refine ⟨rfl, leviBorel_isBorel G I, ?_, ?_,
    ⟨leviBorelProductIso G I, rfl⟩, ⟨leviBorelSemidirectIso G I, fun _ => rfl⟩, ?_⟩
  · rw [← leviBorelRadical_ambient G I]
    exact HopfIdeal.map_comapOfSurjective _ _ _
  · rw [← G.levi_unipotent_eq I]
    ext g
    constructor
    · rintro ⟨hL, hU⟩
      exact ⟨⟨hL, G.unipotent_le_borel hU⟩, hU⟩
    · rintro ⟨⟨hL, _⟩, hU⟩
      exact ⟨hL, hU⟩
  · intro l hl hall
    obtain ⟨hm, hu⟩ := rootSupport_directly_spanned G _
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) l hl hall
    exact ⟨rootSubsetProductChart G _ (LeviRootSpan.isPositiveRootClosed G.rootBase I)
      l hl hall, rootSubsetProductChart_points G _ _ l hl hall, hm, hu⟩

/-- The Levi Borel radical and both multiplication structures over the complex numbers. -/
theorem leviBorel_definition_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) :
    G.leviBorelPoints I = G.leviPoints I ⊓ G.borelPoints ∧
    HopfIdeal.IsBorel ℂ (G.leviAlgebra I).obj (leviBorelIdealInLevi G I) ∧
    (G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I)).map
        (Bialgebra.Quotient.mkBialgHom (G.leviBorelIdeal I).toIdeal) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (G.leviBorelAlgebra I) ∧
    G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) =
      G.leviBorelPoints I ⊓ G.unipotentPoints ∧
    (∃ e : (leviBorelProduct G I).toOver ≅ (leviBorelVariety G I).toOver,
      e.hom = leviBorelMultiplication G I) ∧
    (∃ e : (rootsInLeviBorel G I) ⋊[
        ((rootsInLeviBorel G I).normalizerMonoidHom).comp (Subgroup.inclusion
          ((rootsInLeviBorel G I).normalizer_eq_top ▸ le_top))]
        (torusInLeviBorel G I) ≃* G.leviBorelPoints I,
      ∀ p, (e p : G.points) = (p.left : G.points) * (p.right : G.points)) ∧
    ∀ (l : List (G.rootCharacters (leviPositiveRoots G.rootBase I)))
      (_hl : l.Nodup) (_hall : ∀ i, i ∈ l),
      ∃ e : (affineSpaceVariety ℂ (G.rootCharacters (leviPositiveRoots G.rootBase I))).toOver ≅
          (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
            (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toOver,
        (∀ a : G.rootCharacters (leviPositiveRoots G.rootBase I) → ℂ,
          (rootSubsetPointsMulEquiv G _ _ (Variety.mapPoints e.hom
            ((affineSpaceVarietyPointsEquiv ℂ _).symm a)) : G.points) =
              (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod) ∧
        (∀ f : (i : G.rootCharacters (leviPositiveRoots G.rootBase I)) →
            rootSubgroupPoints G (G.characterRootEquiv
              (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
          (l.map (fun i => (f i : G.points))).prod ∈
            G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
              (LeviRootSpan.isPositiveRootClosed G.rootBase I)) ∧
        ∀ g : G.points, g ∈ G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
            (LeviRootSpan.isPositiveRootClosed G.rootBase I) →
          ∃! f : (i : G.rootCharacters (leviPositiveRoots G.rootBase I)) →
              rootSubgroupPoints G (G.characterRootEquiv
                (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
            (l.map (fun i => (f i : G.points))).prod = g :=
  leviBorel_definition G I

end SchubertOrbits
