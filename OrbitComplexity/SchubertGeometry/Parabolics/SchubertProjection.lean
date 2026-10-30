import OrbitComplexity.SchubertGeometry.Parabolics.Schubert
import OrbitComplexity.SchubertGeometry.Parabolics.Proper

/-! # Proper projections of Schubert varieties

The complete-to-partial flag projection maps each reduced Schubert closure onto its
partial Schubert closure and restricts to a proper morphism.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem projectedCell_range (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (schubertCellInclusion G w ≫ partialFlagMorphism G J).left =
      Set.range (partialSchubertCellInclusion G J w).left := by
  rw [← partialCellProjection_comp G J w]
  change Set.range ((partialSchubertCellInclusion G J w).left ∘
    (partialCellProjection G J w).left) = _
  rw [Set.range_comp, (partialCellProjection G J w).left.surjective.range_eq,
    Set.image_univ]

private theorem projectedSchubert_range (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (schubertInclusion G w ≫ partialFlagMorphism G J).left =
      Set.range (partialSchubertInclusion G J w).left := by
  change Set.range ((partialFlagMorphism G J).left ∘ (schubertInclusion G w).left) = _
  rw [Set.range_comp, schubertInclusion_range, partialSchubertInclusion_range]
  rw [← (partialFlagMorphism G J).left.isClosedMap.closure_image_eq_of_continuous
    (partialFlagMorphism G J).left.continuous]
  congr 1
  rw [← Set.range_comp]
  change Set.range (schubertCellInclusion G w ≫ partialFlagMorphism G J).left = _
  exact projectedCell_range G J w

/-- The parabolic projection restricted to a Schubert variety. -/
def partialSchubertProjection (J : Set G.rootBase.support) (w : G.weylGroup) :
    (schubertVariety G w).toOver ⟶ (partialSchubertVariety G J w).toOver := by
  let i := partialSchubertInclusion G J w
  let f := schubertInclusion G w ≫ partialFlagMorphism G J
  let g := liftPreimmersion (X := (partialFlagVariety G J).scheme)
    (Y := (schubertVariety G w).scheme) (Z := (partialSchubertVariety G J w).scheme)
    i.left f.left (projectedSchubert_range G J w).le
  refine Over.homMk g ?_
  change g ≫ (partialSchubertVariety G J w).toSpec = (schubertVariety G w).toSpec
  have hi : i.left ≫ (partialFlagVariety G J).toSpec =
      (partialSchubertVariety G J w).toSpec := i.w
  rw [← hi, ← Category.assoc]
  dsimp only [g]
  rw [liftPreimmersion_fac]
  exact f.w

/-- The Schubert projection commutes with the ambient flag inclusions. -/
theorem partialSchubertProjection_comp (J : Set G.rootBase.support) (w : G.weylGroup) :
    partialSchubertProjection G J w ≫ partialSchubertInclusion G J w =
      schubertInclusion G w ≫ partialFlagMorphism G J := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (X := (partialFlagVariety G J).scheme)
    (Y := (schubertVariety G w).scheme) (Z := (partialSchubertVariety G J w).scheme)
    (partialSchubertInclusion G J w).left
    (schubertInclusion G w ≫ partialFlagMorphism G J).left
    (projectedSchubert_range G J w).le

/-- The Schubert projection is surjective on scheme points. -/
instance partialSchubertProjection_surjective (J : Set G.rootBase.support) (w : G.weylGroup) :
    Surjective (partialSchubertProjection G J w).left := by
  constructor
  intro y
  have hy : (partialSchubertInclusion G J w).left y ∈
      Set.range (schubertInclusion G w ≫ partialFlagMorphism G J).left := by
    rw [projectedSchubert_range]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (partialSchubertInclusion G J w).left.isEmbedding.injective ?_⟩
  have hc := congrArg Over.Hom.left (partialSchubertProjection_comp G J w)
  exact (congrArg (fun m : (schubertVariety G w).scheme ⟶ (partialFlagVariety G J).scheme =>
    m x) hc).trans hx

/-- The Schubert projection is proper. -/
instance partialSchubertProjection_isProper (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsProper (partialSchubertProjection G J w).left := by
  have : IsProper (schubertVariety G w).toSpec := by
    have hc : (schubertInclusion G w).left ≫ (flagVariety G).toSpec =
        (schubertVariety G w).toSpec := (schubertInclusion G w).w
    rw [← hc]
    infer_instance
  have hw : (partialSchubertProjection G J w).left ≫
      (partialSchubertVariety G J w).toSpec = (schubertVariety G w).toSpec :=
    (partialSchubertProjection G J w).w
  have : IsProper ((partialSchubertProjection G J w).left ≫
      (partialSchubertVariety G J w).toSpec) := by
    rw [hw]
    infer_instance
  exact IsProper.of_comp (partialSchubertProjection G J w).left
    (partialSchubertVariety G J w).toSpec

end SchubertGeometry
