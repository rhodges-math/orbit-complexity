import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionOrbits
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChart
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussBoundary
import OrbitComplexity.GroupActions.Varieties.ProductImages
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The simple opposite boundary in transverse coordinates

The inverse image of the corresponding opposite Schubert variety in the
translated flag chart is the zero section of its additive coordinate.
-/

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonoidalCategory
open ReductiveGroups TauCeti GroupActions Topology

noncomputable section

namespace SchubertGeometry.DeterminantSection

open private SchubertGeometry.DeterminantSection.parameter
  SchubertGeometry.DeterminantSection.complementPoint
  SchubertGeometry.DeterminantSection.chartMap_points from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChart
open private SchubertGeometry.DeterminantSection.constructible_eq_of_points from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussBoundary

private theorem closed_constructible {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X]
    {S : Set X} (hS : IsClosed S) : IsConstructible S :=
  ((TopologicalSpace.NoetherianSpace.isCompact Sᶜ).isConstructible hS.isOpen_compl).of_compl

private theorem equiv_symm_zero {M N : Type*} [Zero M] (e : M ≃ N) (n : N) :
    e.symm n = 0 ↔ n = e 0 := by
  constructor
  · intro h
    exact (e.apply_symm_apply n).symm.trans (congrArg e h)
  · intro h
    exact (congrArg e.symm h).trans (e.symm_apply_apply 0)

universe u
variable {K : Type u} [Field K]

private theorem zero_coordinate_range (X F : Variety K)
    (e : X.toOver ⊗ (additiveVariety K).toOver ≅ F.toOver) :
    Set.range (Variety.mapPoints (X := X) (Y := F)
      (lift (𝟙 X.toOver) (toUnit X.toOver ≫
        (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ e.hom)) =
      {p | Variety.mapPoints
        (e.inv ≫ snd X.toOver (additiveVariety K).toOver) p = additivePointsEquiv K 0} :=
  Variety.zeroSection_points_range X F e.symm

variable [IsAlgClosed K]

private theorem preimage_range_points (X Y Z : Variety K)
    (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver) (x : X.points) :
    f.left (X.pointMap x) ∈ Set.range g.left ↔
      Variety.mapPoints f x ∈ Set.range (Variety.mapPoints g) := by
  have h := Set.ext_iff.mp (Variety.range_mapPoints g) (Variety.mapPoints f x)
  simpa only [Set.mem_preimage, Variety.pointMap_mapPoints] using h.symm

variable [CharZero K] (G : ReductiveGroupData K)

private abbrev complement (i : G.rootBase.support) :=
  rootSubsetVariety G
    {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i)}
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i))

private theorem flag_points (i : G.rootBase.support)
    (x : (oppositeUnipotentVariety G).points) :
    Variety.mapPoints (flagChartMorphism G (oppositionChartPoint G i)) x =
      flagVarietyPointsEquiv G (flagProjection G (oppositionRootLift G i
        (SchubertGeometry.DeterminantSection.complementPoint G i x)
        (SchubertGeometry.DeterminantSection.parameter G i x))) := by
  have hg := (reductivePointsEquiv G).injective
    ((flagChartMap_points G (oppositionChartPoint G i) x).symm.trans
      (SchubertGeometry.DeterminantSection.chartMap_points G i x))
  exact (flagChartMorphism_points G (oppositionChartPoint G i) x).trans
    (congrArg (fun p : G.points => flagVarietyPointsEquiv G (flagProjection G p)) hg)

private theorem cell_in_variety (w : G.weylGroup) (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (X := oppositeSchubertCell G w)
      (Y := flagVariety G) (oppositeSchubertCellInclusion G w))) :
    q ∈ Set.range (Variety.mapPoints (X := oppositeSchubertVariety G w)
      (Y := flagVariety G) (oppositeSchubertInclusion G w)) := by
  have hcell := (Set.ext_iff.mp (Variety.range_mapPoints
    (X := oppositeSchubertCell G w) (Y := flagVariety G) (oppositeSchubertCellInclusion G w)) q).mp
      hq
  have hclosed := (Set.ext_iff.mp (oppositeSchubertInclusion_range G w)
    ((flagVariety G).pointMap q)).mpr (subset_closure hcell)
  exact (Set.ext_iff.mp (Variety.range_mapPoints
    (X := oppositeSchubertVariety G w) (Y := flagVariety G) (oppositeSchubertInclusion G w)) q).mpr
      hclosed

private theorem simple_outside (i : G.rootBase.support) (p : (flagVariety G).scheme)
    (hp : p ∈ Set.range
      (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i)).left) :
    p ∈ (Set.range (flagChartMorphism G 1).left)ᶜ := by
  have hword : simpleWeylWord G.rootBase [i] = RootPairing.weylGroup.ofIdx G.rootSystem i := by
    simp only [simpleWeylWord, mul_one]
  apply (Set.ext_iff.mp (gauss_boundary_schubert G) p).mpr
  exact Set.mem_iUnion.mpr ⟨i, hword.symm ▸ hp⟩

private theorem identity_not_boundary (i : G.rootBase.support) (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (X := oppositeSchubertCell G 1)
      (Y := flagVariety G) (oppositeSchubertCellInclusion G 1))) :
    q ∉ Set.range (Variety.mapPoints
      (X := oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i))
      (Y := flagVariety G)
      (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))) := by
  intro hd
  have hcell := (Set.ext_iff.mp (Variety.range_mapPoints
    (X := oppositeSchubertCell G 1) (Y := flagVariety G) (oppositeSchubertCellInclusion G 1)) q).mp
      hq
  have hbig := (Set.ext_iff.mp (gauss_oppositeCell_range G) ((flagVariety G).pointMap q)).mpr hcell
  have hclosed := (Set.ext_iff.mp (Variety.range_mapPoints
    (X := oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i))
    (Y := flagVariety G)
    (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))) q).mp hd
  exact simple_outside G i _ hclosed hbig

private theorem boundary_points (i : G.rootBase.support)
    (x : (oppositeUnipotentVariety G).points) :
    Variety.mapPoints (flagChartMorphism G (oppositionChartPoint G i)) x ∈
      Set.range (Variety.mapPoints
        (X := oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple
          G i)))
        (Y := flagVariety G)
        (oppositeSchubertInclusion G
          (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i)))) ↔
      SchubertGeometry.DeterminantSection.parameter G i x = 0 := by
  have hflag := flag_points G i x
  constructor
  · intro hd
    by_contra ht
    have hcell := oppositionRootLift_ne_zero_cell G i
      (SchubertGeometry.DeterminantSection.complementPoint G i x)
      (SchubertGeometry.DeterminantSection.complementPoint G i x).property
      (SchubertGeometry.DeterminantSection.parameter G i x) ht
    exact identity_not_boundary G (oppositionSimple G i) _ (hflag.symm ▸ hcell) hd
  · intro ht
    have hcell := oppositionRootLift_zero_cell G i
      (SchubertGeometry.DeterminantSection.complementPoint G i x)
      (SchubertGeometry.DeterminantSection.complementPoint G i x).property
    have hcoord := congrArg (fun t : K => flagVarietyPointsEquiv G
      (flagProjection G (oppositionRootLift G i
        (SchubertGeometry.DeterminantSection.complementPoint G i x) t))) ht
    have hclosed := cell_in_variety G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i)) _ (hcoord.symm ▸ hcell)
    exact hflag.symm ▸ hclosed

/-- The zero section of the additive coordinate in the opposite-unipotent coordinates. -/
def oppositionZeroMap (i : G.rootBase.support) :
    (rootSubsetVariety G
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))).toOver ⟶
      (oppositeUnipotentVariety G).toOver :=
  lift (𝟙 (complement G i).toOver) (toUnit (complement G i).toOver ≫
    (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫
      (oppositeSimpleCoordinates G i).hom

private theorem zero_range (i : G.rootBase.support) :
    Set.range (Variety.mapPoints (X := complement G i) (Y := oppositeUnipotentVariety G)
      (oppositionZeroMap G i)) =
      {p | SchubertGeometry.DeterminantSection.parameter G i p = 0} := by
  have h := zero_coordinate_range (complement G i) (oppositeUnipotentVariety G)
    (oppositeSimpleCoordinates G i)
  ext p
  exact (Set.ext_iff.mp h p).trans (equiv_symm_zero (additivePointsEquiv K)
    (Variety.mapPoints ((oppositeSimpleCoordinates G i).inv ≫ snd _ _) p)).symm

/-- The corresponding simple opposite Schubert variety pulls back to the zero
section of the transverse additive coordinate. -/
theorem oppositionBoundary_preimage (i : G.rootBase.support) :
    (flagChartMorphism G (oppositionChartPoint G i)).left ⁻¹'
      Set.range (oppositeSchubertInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left =
      Set.range (oppositionZeroMap G i).left := by
  have hd : IsClosed (Set.range (oppositeSchubertInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))).left) :=
    (oppositeSchubertInclusion_range G _).symm ▸ isClosed_closure
  apply SchubertGeometry.DeterminantSection.constructible_eq_of_points
    (oppositeUnipotentVariety G)
    (closed_constructible (hd.preimage (flagChartMorphism G (oppositionChartPoint G
      i)).left.continuous))
    (Variety.isConstructible_range (X := complement G i) (Y := oppositeUnipotentVariety G)
      (oppositionZeroMap G i))
  ext x
  exact (preimage_range_points (oppositeUnipotentVariety G)
    (oppositeSchubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i)))
    (flagVariety G) (flagChartMorphism G (oppositionChartPoint G i))
    (oppositeSchubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i)))
      x).trans
      ((boundary_points G i x).trans ((Set.ext_iff.mp (zero_range G i) x).symm.trans
        (Set.ext_iff.mp (Variety.range_mapPoints
          (X := complement G i) (Y := oppositeUnipotentVariety G) (oppositionZeroMap G i)) x)))

end SchubertGeometry.DeterminantSection
