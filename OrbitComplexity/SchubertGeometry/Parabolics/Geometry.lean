import OrbitComplexity.SchubertGeometry.Parabolics.Birational
import OrbitComplexity.SchubertGeometry.Parabolics.Preimage

/-! # Geometry of the partial flag projection

The projective partial flag variety receives a proper surjective equivariant projection.
Its Schubert restrictions have the prescribed cell isomorphisms, birational maps and
scheme inverse images.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions
noncomputable section
universe u
namespace SchubertGeometry
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

attribute [local irreducible] partialFlagVariety partialFlagMorphism partialCellProjection
  ReductiveGroupData.rootBase GroupActions.orbitVariety GroupActions.orbitInclusion
  GroupActions.Variety.closedSubvariety GroupActions.Variety.closedInclusion
  partialSchubertProjection partialCellIso

/-- The partial flag variety is projective; its proper equivariant projection has Schubert
cell isomorphisms, compatible birational restrictions and scheme pullbacks. -/
theorem partialFlag_properties (J : Set G.rootBase.support) :
    IsProper (partialFlagVariety G J).toSpec ∧
    (∃ n : ℕ, ∃ i : (partialFlagVariety G J).toOver ⟶
      (projectiveVariety K (ULift (Fin n))).toOver, IsClosedImmersion i.left) ∧
    Surjective (partialFlagMorphism G J).left ∧
    IsProper (partialFlagMorphism G J).left ∧
    IsModHom (reductiveVariety G).toOver (partialFlagMorphism G J) ∧
    (∀ p : flagPoints G,
      Variety.mapPoints (partialFlagMorphism G J) (flagVarietyPointsEquiv G p) =
        partialFlagPointsEquiv G J (SchubertGeometry.partialFlagProjection G J p)) ∧
    ∀ w : G.weylGroup, IsMinimalRightParabolic G.rootBase J w →
      (∃ e : (schubertCell G w).toOver ≅ (partialSchubertCell G J w).toOver,
        e.hom = partialCellProjection G J w) ∧
      (∃ f : (schubertVariety G w).toOver ⟶ (partialSchubertVariety G J w).toOver,
        f ≫ partialSchubertInclusion G J w =
          schubertInclusion G w ≫ partialFlagMorphism G J ∧
        Surjective f.left ∧ IsProper f.left ∧
        ∃ p : (schubertVariety G w).scheme.PartialIso (partialSchubertVariety G J w).scheme,
          p.IsOver (schubertVariety G w).toSpec (partialSchubertVariety G J w).toSpec ∧
          p.source.ι ≫ f.left = p.iso.hom ≫ p.target.ι) ∧
      ((partialFlagMorphism G J).left ⁻¹' Set.range (partialSchubertInclusion G J w).left =
        Set.range (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left) ∧
      ∃ e : (schubertVariety G (w * longestParabolicElement G.rootBase J)).scheme ≅
          CategoryTheory.Limits.pullback (partialFlagMorphism G J).left
            (partialSchubertInclusion G J w).left,
        e.hom ≫ CategoryTheory.Limits.pullback.fst (partialFlagMorphism G J).left
            (partialSchubertInclusion G J w).left =
          (schubertInclusion G (w * longestParabolicElement G.rootBase J)).left := by
  refine ⟨partialFlagVariety_isProper G J, partialFlag_projective G J,
    partialFlagMorphism_surjective G J, partialFlagMorphism_isProper G J,
    partialFlagMorphism_isModHom G J, partialFlagMorphism_points G J, ?_⟩
  intro w hw
  have hprojection := partialSchubertProjection_properties (K := K) G J w
  refine ⟨⟨partialCellIso G J w hw, partialCellIso_hom G J w hw⟩, ?_,
    partialSchubert_pullback (K := K) G J w hw⟩
  exact ⟨partialSchubertProjection G J w, hprojection.1, hprojection.2.1,
    hprojection.2.2.1, hprojection.2.2.2 hw⟩

end SchubertGeometry
