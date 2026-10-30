import OrbitComplexity.Paper.Deodhar.Components
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixActions
import OrbitComplexity.SchubertGeometry.Cells.OppositeActions
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties

/-! # Torus actions on intrinsic Deodhar components

Prefix projections are torus equivariant and opposite cells are invariant. Their simultaneous
prefix conditions therefore give invariant reduced subvarieties with algebraic torus actions.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups SchubertGeometry GroupActions
namespace SchubertOrbits
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : BruhatIntervals.Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f = Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

private theorem prefix_stable (n : ℕ) (t : (torusVariety G).points)
    (x : (deodharPrefixComponent G expression hred n).points) :
    t • Variety.mapPoints (deodharPrefixInclusion G expression hred n) x ∈
      Set.range (Variety.mapPoints (deodharPrefixInclusion G expression hred n)) := by
  apply (mem_deodharPrefix_points G expression hred n _).mpr
  intro k
  let f : (wordCell G word n).toOver ⟶ (flagVariety G).toOver :=
    wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val))
  have hf : IsModHom (torusVariety G).toOver f := by
    dsimp only [f]
    infer_instance
  have hx := (mem_deodharPrefix_points G expression hred n
    (Variety.mapPoints (deodharPrefixInclusion G expression hred n) x)).mp ⟨x, rfl⟩ k
  change Variety.mapPoints f (t •
    Variety.mapPoints (deodharPrefixInclusion G expression hred n) x) ∈ _
  rw [equivariant_points f t]
  exact oppositeSchubertCell_torus_stable G _ t hx

/-- Every intrinsic prefix component inherits the ordinary algebraic torus action. -/
instance deodharPrefixTorusAction (n : ℕ) :
    ModObj (torusVariety G).toOver (deodharPrefixComponent G expression hred n).toOver :=
  Variety.modObjOfInvariant (torusVariety G) (wordCell G word n)
    (deodharPrefixComponent G expression hred n)
    (deodharPrefixInclusion G expression hred n) (prefix_stable G expression hred n)

/-- The inclusion of an intrinsic prefix component is torus equivariant. -/
instance deodharPrefixInclusion_torus (n : ℕ) :
    IsModHom (torusVariety G).toOver (deodharPrefixInclusion G expression hred n) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ (prefix_stable G expression hred n)

/-- The intrinsic full component inclusion into the flag variety is torus equivariant. -/
instance deodharInclusion_torus :
    IsModHom (torusVariety G).toOver (deodharInclusion G expression hred) := by
  change IsModHom (torusVariety G).toOver
    (deodharPrefixInclusion G expression hred word.length ≫ _)
  infer_instance

end
end SchubertOrbits
