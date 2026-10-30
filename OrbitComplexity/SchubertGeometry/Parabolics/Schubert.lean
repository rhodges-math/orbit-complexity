import OrbitComplexity.SchubertGeometry.Parabolics.Projection
import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints

/-! # Schubert cells and varieties in partial flags

Borel orbits of partial Weyl flags carry reduced locally closed variety structures.
Their closures are reduced integral closed subvarieties. The complete-to-partial
projection restricts to a surjective morphism on each Schubert cell.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry Topology
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The partial flag represented by a chosen Weyl group representative. -/
def partialWeylFlagPoint (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialFlagVariety G J).points :=
  partialFlagPointsEquiv G J (QuotientGroup.mk (G.weylPoint w))

/-- The Borel acts on partial flags through the reductive group action. -/
instance partialFlagBorelAction (J : Set G.rootBase.support) :
    ModObj (borelVariety G).toOver (partialFlagVariety G J).toOver :=
  Mod.scalarRestriction (borelInclusion G) (partialFlagVariety G J).toOver

/-- The Borel action on partial flags is multiplication on parabolic cosets. -/
theorem borelPartialFlag_smul (J : Set G.rootBase.support) (b : (borelVariety G).points)
    (q : partialFlagPoints G J) :
    b • partialFlagPointsEquiv G J q = partialFlagPointsEquiv G J
      ((borelPointsMulEquiv G b : G.points) • q) := by
  rw [Variety.restricted_smul (borelInclusion G), borelInclusion_points]
  exact partialFlag_smul G J _ q

/-- A partial Schubert cell is the reduced Borel orbit of its Weyl flag. -/
abbrev partialSchubertCell (J : Set G.rootBase.support) (w : G.weylGroup) :
    GroupActions.Variety K :=
  orbitVariety (borelVariety G) (partialFlagVariety G J) (partialWeylFlagPoint G J w)

/-- The locally closed inclusion of a partial Schubert cell. -/
abbrev partialSchubertCellInclusion (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialSchubertCell G J w).toOver ⟶ (partialFlagVariety G J).toOver :=
  orbitInclusion (borelVariety G) (partialFlagVariety G J) (partialWeylFlagPoint G J w)

/-- The closed support of a partial Schubert variety is the closure of its cell. -/
def partialSchubertSupport (J : Set G.rootBase.support) (w : G.weylGroup) :
    TopologicalSpace.Closeds (partialFlagVariety G J).scheme :=
  ⟨closure (Set.range (partialSchubertCellInclusion G J w).left), isClosed_closure⟩

/-- The partial Schubert variety is the reduced closure of its Borel orbit. -/
abbrev partialSchubertVariety (J : Set G.rootBase.support) (w : G.weylGroup) :
    GroupActions.Variety K :=
  (partialFlagVariety G J).closedSubvariety (partialSchubertSupport G J w)

/-- The closed inclusion of a partial Schubert variety. -/
abbrev partialSchubertInclusion (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialSchubertVariety G J w).toOver ⟶ (partialFlagVariety G J).toOver :=
  (partialFlagVariety G J).closedInclusion (partialSchubertSupport G J w)

/-- The image of a partial Schubert variety is the closure of its cell. -/
theorem partialSchubertInclusion_range (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (partialSchubertInclusion G J w).left =
      closure (Set.range (partialSchubertCellInclusion G J w).left) :=
  Variety.closedInclusion_range _ _

/-- A partial Schubert cell is integral. -/
instance partialSchubertCellIntegral (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsIntegral (partialSchubertCell G J w).scheme :=
  inferInstanceAs (IsIntegral (orbitVariety (borelVariety G) (partialFlagVariety G J)
    (partialWeylFlagPoint G J w)).scheme)

/-- A partial Schubert variety is integral. -/
instance partialSchubertVarietyIntegral (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsIntegral (partialSchubertVariety G J w).scheme := by
  have hr : IsIrreducible (Set.range (partialSchubertCellInclusion G J w).left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (partialSchubertCell G J w).scheme).image
        (partialSchubertCellInclusion G J w).left
        (partialSchubertCellInclusion G J w).left.continuous.continuousOn
  have : IrreducibleSpace (closure (Set.range (partialSchubertCellInclusion G J w).left)) :=
    isIrreducible_iff_irreducibleSpace.mp hr.closure
  let e := (partialSchubertInclusion G J w).left.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (partialSchubertInclusion_range G J w))
  have : IrreducibleSpace (partialSchubertVariety G J w).scheme :=
    e.irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The rational image of a partial Schubert cell is its Borel orbit. -/
theorem partialSchubertCell_points_range (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (Variety.mapPoints (partialSchubertCellInclusion G J w)) =
      MulAction.orbit (borelVariety G).points (partialWeylFlagPoint G J w) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact (orbitPointsEquiv (borelVariety G) (partialFlagVariety G J)
      (partialWeylFlagPoint G J w) z).property
  · intro hp
    obtain ⟨z, hz⟩ := (orbitPointsEquiv (borelVariety G) (partialFlagVariety G J)
      (partialWeylFlagPoint G J w)).surjective ⟨p, hp⟩
    exact ⟨z, congrArg Subtype.val hz⟩

private theorem projection_weyl (J : Set G.rootBase.support) (w : G.weylGroup) :
    Variety.mapPoints (partialFlagMorphism G J) (weylFlagPoint G w) =
      partialWeylFlagPoint G J w :=
  partialFlagMorphism_points G J (flagProjection G (G.weylPoint w))

private theorem projection_borel_smul (J : Set G.rootBase.support)
    (b : (borelVariety G).points) (x : (flagVariety G).points) :
    Variety.mapPoints (partialFlagMorphism G J) (b • x) =
      b • Variety.mapPoints (partialFlagMorphism G J) x := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective x
  rw [borelFlag_smul, partialFlagMorphism_points, partialFlagProjection_smul,
    ← borelPartialFlag_smul, partialFlagMorphism_points]

private theorem projectedCell_points (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (Variety.mapPoints (schubertCellInclusion G w ≫ partialFlagMorphism G J)) =
      MulAction.orbit (borelVariety G).points (partialWeylFlagPoint G J w) := by
  have hf : Variety.mapPoints (schubertCellInclusion G w ≫ partialFlagMorphism G J) =
      Variety.mapPoints (partialFlagMorphism G J) ∘
        Variety.mapPoints (schubertCellInclusion G w) :=
    funext (Variety.mapPoints_comp _ _)
  rw [hf, Set.range_comp, schubertCell_points_range]
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hy
    rw [← hb, projection_borel_smul, projection_weyl]
    exact MulAction.mem_orbit _ b
  · intro hp
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hp
    refine ⟨b • weylFlagPoint G w, MulAction.mem_orbit _ b, ?_⟩
    rw [projection_borel_smul, projection_weyl]
    exact hb

private theorem projectedCell_range (J : Set G.rootBase.support) (w : G.weylGroup) :
    Set.range (schubertCellInclusion G w ≫ partialFlagMorphism G J).left =
      Set.range (partialSchubertCellInclusion G J w).left := by
  apply Variety.range_eq_of_mapPoints
  rw [projectedCell_points, partialSchubertCell_points_range]

/-- The regular projection from a Schubert cell to its partial Schubert cell. -/
def partialCellProjection (J : Set G.rootBase.support) (w : G.weylGroup) :
    (schubertCell G w).toOver ⟶ (partialSchubertCell G J w).toOver := by
  let i := partialSchubertCellInclusion G J w
  let f := schubertCellInclusion G w ≫ partialFlagMorphism G J
  let g := liftPreimmersion (X := (partialFlagVariety G J).scheme)
    (Y := (schubertCell G w).scheme) (Z := (partialSchubertCell G J w).scheme)
    i.left f.left (projectedCell_range G J w).le
  refine Over.homMk g ?_
  change g ≫ (partialSchubertCell G J w).toSpec = (schubertCell G w).toSpec
  have hi : i.left ≫ (partialFlagVariety G J).toSpec =
      (partialSchubertCell G J w).toSpec := i.w
  rw [← hi, ← Category.assoc]
  dsimp only [g]
  rw [liftPreimmersion_fac]
  exact f.w

/-- The cell projection commutes with the ambient flag inclusions. -/
theorem partialCellProjection_comp (J : Set G.rootBase.support) (w : G.weylGroup) :
    partialCellProjection G J w ≫ partialSchubertCellInclusion G J w =
      schubertCellInclusion G w ≫ partialFlagMorphism G J := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (X := (partialFlagVariety G J).scheme)
    (Y := (schubertCell G w).scheme) (Z := (partialSchubertCell G J w).scheme)
    (partialSchubertCellInclusion G J w).left
    (schubertCellInclusion G w ≫ partialFlagMorphism G J).left
    (projectedCell_range G J w).le

/-- The cell projection is surjective on scheme points. -/
instance partialCellProjection_surjective (J : Set G.rootBase.support) (w : G.weylGroup) :
    Surjective (partialCellProjection G J w).left := by
  constructor
  intro y
  have hy : (partialSchubertCellInclusion G J w).left y ∈
      Set.range (schubertCellInclusion G w ≫ partialFlagMorphism G J).left := by
    rw [projectedCell_range]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (partialSchubertCellInclusion G J w).left.isEmbedding.injective ?_⟩
  have hc := congrArg Over.Hom.left (partialCellProjection_comp G J w)
  exact (congrArg (fun m : (schubertCell G w).scheme ⟶ (partialFlagVariety G J).scheme =>
    m x) hc).trans hx

end SchubertGeometry
