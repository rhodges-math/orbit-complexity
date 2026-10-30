import OrbitComplexity.SchubertGeometry.Parabolics.Schubert
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.GroupActions.Actions.HomogeneousSmooth
import OrbitComplexity.GroupActions.Actions.EquivariantPoints

/-! # Borel actions on partial Schubert cells

The projection of a Schubert cell to a partial flag variety is equivariant and smooth.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
universe u

private theorem map_smul {K : Type u} [Field K] (H X Y : GroupActions.Variety K)
    [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem cellTrans (w : G.weylGroup) (a b : (schubertCell G w).points) :
    ∃ h : (borelVariety G).points, h • a = b := by
  obtain ⟨a', ha⟩ := MulAction.mem_orbit_iff.mp
    (orbitPointsEquiv (borelVariety G) (flagVariety G) (weylFlagPoint G w) a).property
  obtain ⟨b', hb⟩ := MulAction.mem_orbit_iff.mp
    (orbitPointsEquiv (borelVariety G) (flagVariety G) (weylFlagPoint G w) b).property
  change a' • weylFlagPoint G w = Variety.mapPoints (schubertCellInclusion G w) a at ha
  change b' • weylFlagPoint G w = Variety.mapPoints (schubertCellInclusion G w) b at hb
  refine ⟨b' * a'⁻¹, ?_⟩
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
  rw [map_smul (borelVariety G) (schubertCell G w) (flagVariety G)
    (schubertCellInclusion G w), ← ha, ← hb]
  simp only [mul_smul, inv_smul_smul]

private theorem cellStable (J : Set G.rootBase.support) (w : G.weylGroup)
    (b : (borelVariety G).points) (y : (partialSchubertCell G J w).points) :
    b • Variety.mapPoints (partialSchubertCellInclusion G J w) y ∈
      Set.range (Variety.mapPoints (partialSchubertCellInclusion G J w)) := by
  rw [partialSchubertCell_points_range]
  exact MulAction.mem_orbit_of_mem_orbit b
    (orbitPointsEquiv (borelVariety G) (partialFlagVariety G J)
      (partialWeylFlagPoint G J w) y).property

/-- The Borel action restricts to each partial Schubert cell. -/
instance partialSchubertCellBorelAction (J : Set G.rootBase.support) (w : G.weylGroup) :
    ModObj (borelVariety G).toOver (partialSchubertCell G J w).toOver :=
  Variety.modObjOfInvariant (borelVariety G) (partialFlagVariety G J)
    (partialSchubertCell G J w) (partialSchubertCellInclusion G J w) (cellStable G J w)

/-- The inclusion of a partial Schubert cell respects the Borel action. -/
instance partialSchubertCellEquivariant (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsModHom (borelVariety G).toOver (partialSchubertCellInclusion G J w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ (cellStable G J w)

private theorem projection_borel_smul (J : Set G.rootBase.support)
    (b : (borelVariety G).points) (x : (flagVariety G).points) :
    Variety.mapPoints (partialFlagMorphism G J) (b • x) =
      b • Variety.mapPoints (partialFlagMorphism G J) x := by
  let : IsModHom (reductiveVariety G).toOver (partialFlagMorphism G J) :=
    partialFlagMorphism_isModHom G J
  calc
    _ = Variety.mapPoints (partialFlagMorphism G J)
        (Variety.mapPoints (borelInclusion G) b • x) :=
      congrArg _ (Variety.restricted_smul (borelInclusion G) (flagVariety G) b x)
    _ = Variety.mapPoints (borelInclusion G) b •
        Variety.mapPoints (partialFlagMorphism G J) x :=
      map_smul (reductiveVariety G) (flagVariety G) (partialFlagVariety G J)
        (partialFlagMorphism G J) _ _
    _ = _ := (Variety.restricted_smul (borelInclusion G) (partialFlagVariety G J) b
      (Variety.mapPoints (partialFlagMorphism G J) x)).symm

/-- Projection from a Schubert cell respects the Borel action. -/
instance partialCellProjection_isModHom (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsModHom (borelVariety G).toOver (partialCellProjection G J w) := by
  apply Variety.isModHom_of_points (borelVariety G) (schubertCell G w)
    (partialSchubertCell G J w) (partialCellProjection G J w)
  intro h x
  have hfac (y : (schubertCell G w).points) :
      Variety.mapPoints (partialSchubertCellInclusion G J w)
          (Variety.mapPoints (partialCellProjection G J w) y) =
        Variety.mapPoints (partialFlagMorphism G J)
          (Variety.mapPoints (schubertCellInclusion G w) y) := by
    have hc := congrArg (fun f => Variety.mapPoints f y) (partialCellProjection_comp G J w)
    simpa only [Variety.mapPoints_comp] using hc
  apply Variety.mapPoints_injective_of_mono (partialSchubertCellInclusion G J w)
  rw [hfac, map_smul (borelVariety G) (partialSchubertCell G J w)
      (partialFlagVariety G J) (partialSchubertCellInclusion G J w), hfac,
    map_smul (borelVariety G) (schubertCell G w) (flagVariety G)
      (schubertCellInclusion G w), projection_borel_smul]

/-- Projection from a Schubert cell to its partial flag image is smooth. -/
theorem partialCellProjection_smooth (J : Set G.rootBase.support) (w : G.weylGroup) :
    Smooth (partialCellProjection G J w).left := by
  have : IsDominant (partialCellProjection G J w).left := inferInstance
  exact smooth_of_transitive (borelVariety G) (schubertCell G w)
    (partialSchubertCell G J w) (partialCellProjection G J w) (cellTrans G w)

end SchubertGeometry
