import OrbitComplexity.SchubertGeometry.FlagVariety.ChartMorphisms
import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.GroupActions.Actions.OrbitIso
import OrbitComplexity.GroupActions.Complexity.Toric

/-! # Schubert varieties as initial Richardson varieties

The opposite identity cell contains the base open unipotent chart and is dense.
Reduced intersection with its closure identifies the initial Richardson variety
with the corresponding Schubert variety, compatibly with the torus actions.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem chart_in_opposite_one :
    Set.range (flagChartMorphism G 1).left ⊆
      Set.range (oppositeSchubertCellInclusion G 1).left := by
  apply Variety.range_subset_of_mapPoints
  rintro _ ⟨u, rfl⟩
  rw [flagChartMorphism_points, oppositeSchubertCell_points_range]
  let p := oppositeUnipotentPointsMulEquiv G u
  let b := (oppositeBorelPointsMulEquiv G).symm
    ⟨p, G.oppositeUnipotent_le_oppositeBorel p.property⟩
  have hb : (oppositeBorelPointsMulEquiv G b : G.points) = p :=
    congrArg Subtype.val ((oppositeBorelPointsMulEquiv G).apply_symm_apply _)
  have hw : G.weylPoint 1 = 1 := by rw [G.weylPoint_eq, weylElementPoint_one]
  refine MulAction.mem_orbit_iff.mpr ⟨b, ?_⟩
  rw [weylFlagPoint, oppositeBorelFlag_smul, hw]
  change flagVarietyPointsEquiv G (flagProjection G
      ((oppositeBorelPointsMulEquiv G b : G.points) * 1)) =
    flagVarietyPointsEquiv G (flagProjection G
      (1 * (oppositeUnipotentPointsMulEquiv G u : G.points)))
  rw [mul_one, one_mul, hb]

/-- The identity opposite Schubert variety has the whole flag variety as support. -/
theorem oppositeSchubertSupport_one : oppositeSchubertSupport G 1 = ⊤ := by
  have : Nonempty (oppositeUnipotentVariety G).toOver.left := by
    change Nonempty (oppositeUnipotentVariety G).scheme
    exact ⟨(oppositeUnipotentVariety G).pointMap 1⟩
  have : PreirreducibleSpace (flagVariety G).toOver.left := by
    change PreirreducibleSpace (flagVariety G).scheme
    infer_instance
  have hd : Dense (Set.range (flagChartMorphism G 1).left) :=
    (flagChartMorphism G 1).left.isOpenEmbedding.2.dense (Set.range_nonempty _)
  apply SetLike.coe_injective
  apply Set.eq_univ_iff_forall.mpr
  intro q
  exact closure_mono (chart_in_opposite_one G) (hd q)

private theorem richardson_one_range (w : G.weylGroup) :
    Set.range (richardsonInclusion G 1 w).left = Set.range (schubertInclusion G w).left := by
  rw [richardsonInclusion_range, oppositeSchubertInclusion_range]
  have htop : closure (Set.range (oppositeSchubertCellInclusion G 1).left) = Set.univ :=
    congrArg (fun Z : TopologicalSpace.Closeds (flagVariety G).scheme =>
      (Z : Set (flagVariety G).scheme)) (oppositeSchubertSupport_one G)
  rw [htop, Set.inter_univ]

private theorem richardson_one_points (w : G.weylGroup) :
    Set.range (Variety.mapPoints (richardsonInclusion G 1 w)) =
      Set.range (Variety.mapPoints (schubertInclusion G w)) := by
  rw [Variety.range_mapPoints, Variety.range_mapPoints, richardson_one_range]

/-- The initial Richardson variety is isomorphic to the corresponding Schubert variety. -/
def richardsonSchubertIso (w : G.weylGroup) :
    (richardsonVariety G 1 w).toOver ≅ (schubertVariety G w).toOver :=
  Variety.pointImageIso (richardsonInclusion G 1 w) (schubertInclusion G w)
    (richardson_one_points G w)

/-- The initial Richardson isomorphism commutes with the closed inclusions in the flag variety. -/
@[reassoc]
theorem richardsonSchubertIso_hom_comp (w : G.weylGroup) :
    (richardsonSchubertIso G w).hom ≫ schubertInclusion G w =
      richardsonInclusion G 1 w :=
  Variety.pointImageIso_hom_comp _ _ (richardson_one_points G w)

attribute [local irreducible] richardsonSchubertIso

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f = Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

/-- The initial Richardson isomorphism is equivariant for the ordinary torus actions. -/
instance richardsonSchubertIso_torus (w : G.weylGroup) :
    IsModHom (torusVariety G).toOver (richardsonSchubertIso G w).hom := by
  let f := (richardsonSchubertIso G w).hom
  have hfp (p : (richardsonVariety G 1 w).points) :
      Variety.mapPoints (schubertInclusion G w) (Variety.mapPoints f p) =
        Variety.mapPoints (richardsonInclusion G 1 w) p := by
    have hc := Variety.mapPoints_comp (X := richardsonVariety G 1 w)
      (Y := schubertVariety G w) (Z := flagVariety G) f (schubertInclusion G w) p
    have hf := congrArg (fun g : (richardsonVariety G 1 w).toOver ⟶
        (flagVariety G).toOver => Variety.mapPoints
          (X := richardsonVariety G 1 w) (Y := flagVariety G) g p)
      (richardsonSchubertIso_hom_comp G w)
    exact hc.symm.trans hf
  apply Variety.isModHom_of_points (torusVariety G) (richardsonVariety G 1 w)
    (schubertVariety G w) f
  intro t q
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  exact (hfp (t • q)).trans
    ((equivariant_points (richardsonInclusion G 1 w) t q).trans
      ((congrArg (fun p : (flagVariety G).points => t • p) (hfp q).symm).trans
        (equivariant_points (schubertInclusion G w) t (Variety.mapPoints f q)).symm))

/-- Initial Richardson and Schubert varieties have the same torus complexity. -/
theorem torus_richardson_one_complexity (w : G.weylGroup) :
    torusComplexity G (richardsonVariety G 1 w) = torusComplexity G (schubertVariety G w) :=
  (minOrbitCodim_iso (torusVariety G) (richardsonSchubertIso G w)).symm

end SchubertGeometry
