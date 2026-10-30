import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Varieties.BorelPoints

/-! # Regular Borel sections of Schubert cells

The unipotent coordinates of a Schubert cell give a regular Borel-valued section of
its Weyl-flag orbit morphism.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup)

private theorem root_borel_range : Set.range (schubertUnipotentInclusion G w).left ⊆
    Set.range (borelInclusion G).left := by
  apply Variety.range_subset_of_mapPoints
  rintro _ ⟨p, rfl⟩
  let u : schubertUnipotentPoints G w := schubertUnipotentPointsEquiv G w p
  have hu : (u : G.points) ∈ G.borelPoints := G.unipotent_le_borel
    (G.rootSubsetPoints_le_unipotent _ _ u.property)
  let b := (borelPointsMulEquiv G).symm ⟨u, hu⟩
  refine ⟨b, ?_⟩
  have hb : (borelPointsMulEquiv G b : G.points) = u :=
    congrArg Subtype.val ((borelPointsMulEquiv G).apply_symm_apply ⟨u, hu⟩)
  rw [borelInclusion_points, hb]
  exact (rootSubsetInclusion_points G _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) p).symm

private def rootBorelMap : (schubertUnipotent G w).toOver ⟶ (borelVariety G).toOver := by
  let d : (schubertUnipotent G w).scheme ⟶ (reductiveVariety G).scheme :=
    (schubertUnipotentInclusion G w).left
  let j : (borelVariety G).scheme ⟶ (reductiveVariety G).scheme := (borelInclusion G).left
  have hr : Set.range d ⊆ Set.range j := root_borel_range G w
  let b := liftPreimmersion j d hr
  have hb : b ≫ j = d := liftPreimmersion_fac j d hr
  exact Over.homMk b (by
    rw [← (borelInclusion G).w, ← Category.assoc]
    change (b ≫ j) ≫ (reductiveVariety G).toSpec = _
    rw [hb]
    exact (schubertUnipotentInclusion G w).w)

private theorem rootBorelMap_comp : rootBorelMap G w ≫ borelInclusion G =
    schubertUnipotentInclusion G w := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac _ _ (root_borel_range G w)

private def cellBorelSection : (schubertCell G w).toOver ⟶ (borelVariety G).toOver :=
  (schubertCellIso G w).inv ≫ rootBorelMap G w

private theorem rootBorelMap_orbit : rootBorelMap G w ≫
    Variety.orbitMorphism (borelVariety G) (flagVariety G) (weylFlagPoint G w) =
      schubertRootMorphism G w := by
  apply Variety.mapPoints_injective
  funext p
  rw [Variety.mapPoints_comp, Variety.mapPoints_orbitMorphism,
    schubertRootMorphism, Variety.mapPoints_comp, Variety.mapPoints_orbitMorphism]
  rw [Variety.restricted_smul (borelInclusion G), ← Variety.mapPoints_comp,
    rootBorelMap_comp]

private theorem cellBorelSection_orbit : cellBorelSection G w ≫
    Variety.orbitMorphism (borelVariety G) (flagVariety G) (weylFlagPoint G w) =
      schubertCellInclusion G w := by
  rw [cellBorelSection, Category.assoc, rootBorelMap_orbit,
    ← schubertCellIso_hom_comp, Iso.inv_hom_id_assoc]

/-- A regular Borel-valued section of the Weyl-flag orbit map. -/
def schubertCellBorelSection : (schubertCell G w).toOver ⟶ (borelVariety G).toOver :=
  cellBorelSection G w

/-- The regular orbit section maps to the Schubert-cell inclusion. -/
theorem schubertCellBorelSection_orbit : schubertCellBorelSection G w ≫
    Variety.orbitMorphism (borelVariety G) (flagVariety G) (weylFlagPoint G w) =
      schubertCellInclusion G w := cellBorelSection_orbit G w

end SchubertGeometry
