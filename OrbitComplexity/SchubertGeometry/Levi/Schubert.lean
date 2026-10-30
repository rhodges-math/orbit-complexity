import OrbitComplexity.SchubertGeometry.Levi.Cells
import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.SchubertGeometry.Parabolics.BruhatClosure
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.GroupActions.Actions.StabilizerImages
import OrbitComplexity.GroupActions.Actions.OrbitDimensionGeneral

/-! # Levi--Borel orbits in Schubert closures

Borel stability restricts the Levi--Borel action to each Schubert variety.
Lower-cell immersions preserve the dimensions of its Levi--Borel orbits.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem leviBorel_schubert_stable (I : Set G.rootBase.support) (w : G.weylGroup)
    (b : (leviBorelVariety G I).points) (q : (schubertVariety G w).points) :
    b • Variety.mapPoints (schubertInclusion G w) q ∈
      Set.range (Variety.mapPoints (schubertInclusion G w)) := by
  let bp := (borelPointsMulEquiv G).symm
    ⟨leviBorelPointsMulEquiv G I b, (leviBorelPointsMulEquiv G I b).property.2⟩
  have he : b • Variety.mapPoints (schubertInclusion G w) q =
      bp • Variety.mapPoints (schubertInclusion G w) q := by
    obtain ⟨f, hf⟩ := (flagVarietyPointsEquiv G).surjective
      (Variety.mapPoints (schubertInclusion G w) q)
    rw [← hf, leviBorelFlag_smul, flagVarietyAction_points, borelFlag_smul]
    simp only [bp, MulEquiv.apply_symm_apply]
  rw [he]
  exact schubertVariety_stable G w bp ⟨q, rfl⟩

/-- The Levi--Borel action restricts algebraically to every Schubert variety. -/
instance leviBorelSchubertAction (I : Set G.rootBase.support) (w : G.weylGroup) :
    ModObj (leviBorelVariety G I).toOver (schubertVariety G w).toOver :=
  Variety.modObjOfInvariant (leviBorelVariety G I) (flagVariety G) (schubertVariety G w)
    (schubertInclusion G w) (leviBorel_schubert_stable G I w)

/-- The Schubert variety inclusion is equivariant for its Levi--Borel action. -/
instance leviBorelSchubertEquivariant (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsModHom (leviBorelVariety G I).toOver (schubertInclusion G w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ _

/-- The Levi--Borel action on a Schubert variety agrees with the ambient flag action. -/
theorem leviBorelSchubert_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (b : (leviBorelVariety G I).points) (q : (schubertVariety G w).points) :
    Variety.mapPoints (schubertInclusion G w) (b • q) =
      b • Variety.mapPoints (schubertInclusion G w) q :=
  Variety.modObjOfInvariant_smul _ _ _ _ _ b q

private theorem cell_range_le (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) :
    Set.range (schubertCellInclusion G u).left ⊆ Set.range (schubertInclusion G w).left := by
  apply Variety.range_subset_of_mapPoints
  intro q hq
  rw [schubertVariety_points_cells]
  exact Set.mem_iUnion₂.mpr ⟨u, huw, hq⟩

/-- A lower Bruhat cell maps to its containing Schubert variety. -/
def schubertCellOfLE (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) :
    (schubertCell G u).toOver ⟶ (schubertVariety G w).toOver :=
  Over.homMk
    (liftPreimmersion (X := (flagVariety G).scheme)
      (Y := (schubertCell G u).scheme) (Z := (schubertVariety G w).scheme)
      (schubertInclusion G w).left (schubertCellInclusion G u).left
      (cell_range_le G u w huw)) (by
    rw [← (schubertInclusion G w).w, ← Category.assoc, liftPreimmersion_fac]
    exact (schubertCellInclusion G u).w)

/-- The lower-cell inclusion commutes with its ambient flag inclusions. -/
@[reassoc]
theorem schubertCellOfLE_comp (u w : G.weylGroup) (huw : WeylBruhatLE G.rootBase u w) :
    schubertCellOfLE G u w huw ≫ schubertInclusion G w = schubertCellInclusion G u := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (X := (flagVariety G).scheme)
    (Y := (schubertCell G u).scheme) (Z := (schubertVariety G w).scheme)
    (schubertInclusion G w).left
    (schubertCellInclusion G u).left (cell_range_le G u w huw)

/-- The map of a lower cell into a Schubert variety is an immersion. -/
instance schubertCellOfLE_isImmersion (u w : G.weylGroup)
    (huw : WeylBruhatLE G.rootBase u w) :
    IsImmersion (schubertCellOfLE G u w huw).left := by
  have : IsImmersion (schubertCellInclusion G u).left :=
    { isLocallyClosed_range := by
        rw [GroupActions.orbitInclusion_range]
        exact orbitImage_locallyClosed _ _ _ }
  have : IsImmersion ((schubertCellOfLE G u w huw).left ≫ (schubertInclusion G w).left) := by
    change IsImmersion (schubertCellOfLE G u w huw ≫ schubertInclusion G w).left
    rw [schubertCellOfLE_comp]
    infer_instance
  exact IsImmersion.of_comp _ (schubertInclusion G w).left

/-- Lower-cell inclusions commute with the Levi--Borel actions. -/
instance schubertCellOfLE_isModHom (I : Set G.rootBase.support) (u w : G.weylGroup)
    (huw : WeylBruhatLE G.rootBase u w) :
    IsModHom (leviBorelVariety G I).toOver (schubertCellOfLE G u w huw) := by
  apply Variety.isModHom_of_points
  intro b q
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  rw [← Variety.mapPoints_comp, schubertCellOfLE_comp, leviBorelSchubert_smul,
    ← Variety.mapPoints_comp, schubertCellOfLE_comp]
  exact leviBorelCell_smul G I u b q

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_mapPoints {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (t : H.points) (x : X.points) :
    Variety.mapPoints f (t • x) = t • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (t • x) ≫ f = Y.pointsEquivOverHom (t • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom t) (X.pointsEquivOverHom x)

omit [CharZero K] in
private theorem equivariant_orbitNatDim {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] [Mono f.left] (x : X.points) :
    orbitNatDim H Y (Variety.mapPoints f x) = orbitNatDim H X x := by
  have hs : Set.range (Variety.mapPoints (stabilizerInclusion H X x)) =
      Set.range (Variety.mapPoints (stabilizerInclusion H Y (Variety.mapPoints f x))) := by
    rw [stabilizerInclusion_points_range, stabilizerInclusion_points_range]
    ext t
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    rw [← equivariant_mapPoints f t x]
    exact (Variety.mapPoints_injective_of_mono f).eq_iff.symm
  let e := Variety.pointImageIso (stabilizerInclusion H X x)
    (stabilizerInclusion H Y (Variety.mapPoints f x)) hs
  have hd := Variety.dim_eq_of_iso (stabilizerVariety H X x) e
  rw [← (stabilizerVariety H X x).natDim_cast,
    ← (stabilizerVariety H Y (Variety.mapPoints f x)).natDim_cast] at hd
  have hd' := ENat.natCast_inj.mp (WithBot.coe_inj.mp hd)
  have hx := groupNatDim_eq_orbit_add H X x
  have hy := groupNatDim_eq_orbit_add H Y (Variety.mapPoints f x)
  omega

/-- Viewing a lower cell inside a Schubert variety preserves its Levi--Borel orbit dimensions. -/
theorem schubertCellOfLE_orbitNatDim (I : Set G.rootBase.support) (u w : G.weylGroup)
    (huw : WeylBruhatLE G.rootBase u w) (q : (schubertCell G u).points) :
    orbitNatDim (leviBorelVariety G I) (schubertVariety G w)
        (Variety.mapPoints (schubertCellOfLE G u w huw) q) =
      orbitNatDim (leviBorelVariety G I) (schubertCell G u) q :=
  equivariant_orbitNatDim (schubertCellOfLE G u w huw) q

end SchubertGeometry
