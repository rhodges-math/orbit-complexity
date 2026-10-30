import OrbitComplexity.SchubertGeometry.Levi.Actions
import OrbitComplexity.BruhatIntervals.Order.Descents
import OrbitComplexity.SchubertGeometry.Parabolics.Preimage
import OrbitComplexity.SchubertGeometry.Levi.Center
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties

/-! # Levi actions on partial Schubert varieties

The longest parabolic suffix determines the stabilizer of a partial Schubert variety.
The corresponding Levi subgroups act regularly on that reduced variety.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem parabolic_mono {I J : Set G.rootBase.support} (h : I ⊆ J) :
    standardParabolicPoints G I ≤ standardParabolicPoints G J := by
  unfold standardParabolicPoints
  exact sup_le_sup le_rfl (Subgroup.closure_mono (Set.image_mono h))

private theorem levi_le_parabolic (I : Set G.rootBase.support) :
    G.leviPoints I ≤ standardParabolicPoints G I := by
  rw [standardParabolicPoints, ← levi_sup_borel_eq G I]
  exact le_sup_left

/-- Restricting the reductive action gives the Levi action on partial flags. -/
instance leviPartialFlagAction (I J : Set G.rootBase.support) :
    ModObj (leviVariety G I).toOver (partialFlagVariety G J).toOver :=
  Mod.scalarRestriction (leviInclusion G I) (partialFlagVariety G J).toOver

/-- The restricted Levi action has the same ambient group point. -/
theorem leviPartialFlag_smul (I J : Set G.rootBase.support)
    (l : (leviVariety G I).points) (q : (partialFlagVariety G J).points) :
    l • q = reductivePointsMulEquiv G (leviPointsMulEquiv G I l) • q :=
  (Variety.restricted_smul (leviInclusion G I) (partialFlagVariety G J) l q).trans
    (congrArg (fun g => g • q) (leviInclusion_points G I l))

/-- The stabilizer of a partial Schubert variety is determined by its longest suffix. -/
theorem partialSchubertStabilizer_eq (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    MulAction.stabilizer G.points ((partialFlagPointsEquiv G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w))) =
        standardParabolicPoints G (BruhatIntervals.leftDescents
          (weylCoxeterSystem G.rootBase) (w * longestParabolicElement G.rootBase J)) := by
  have hset : (partialFlagPointsEquiv G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) =
        partialSchubertPoints G J w := partialSchubert_points G J w
  rw [hset]
  exact partialSchubert_stabilizer G J w hw

private theorem levi_stable (I J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w)
    (hdesc : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J))
    (l : (leviVariety G I).points) (y : (partialSchubertVariety G J w).points) :
    l • Variety.mapPoints (partialSchubertInclusion G J w) y ∈
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) := by
  have hL : G.leviPoints I ≤ MulAction.stabilizer G.points
      ((partialFlagPointsEquiv G J) ⁻¹'
        Set.range (Variety.mapPoints (partialSchubertInclusion G J w))) := by
    rw [partialSchubertStabilizer_eq G J w hw]
    exact (levi_le_parabolic G I).trans (parabolic_mono G hdesc)
  obtain ⟨q, he⟩ := (partialFlagPointsEquiv G J).surjective
    (Variety.mapPoints (partialSchubertInclusion G J w) y)
  have hq : q ∈ (partialFlagPointsEquiv G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) := ⟨y, he.symm⟩
  have hstable := (MulAction.le_stabilizer_iff_smul_le
    ((partialFlagPointsEquiv G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w)))
    (G.leviPoints I)).mp hL
  have hs := hstable (leviPointsMulEquiv G I l)
    (leviPointsMulEquiv G I l).property ⟨q, hq, rfl⟩
  change partialFlagPointsEquiv G J ((leviPointsMulEquiv G I l : G.points) • q) ∈
    Set.range (Variety.mapPoints (partialSchubertInclusion G J w)) at hs
  rw [← partialFlag_smul G J (leviPointsMulEquiv G I l : G.points) q,
    ← leviPartialFlag_smul G I J l (partialFlagPointsEquiv G J q), he] at hs
  exact hs

/-- A Levi subgroup contained in the stabilizer acts on the partial Schubert variety. -/
@[instance_reducible]
def partialSchubertLeviAction (I J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w)
    (hdesc : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J)) :
    ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver :=
  Variety.modObjOfInvariant (leviVariety G I) (partialFlagVariety G J)
    (partialSchubertVariety G J w) (partialSchubertInclusion G J w)
      (levi_stable G I J w hw hdesc)

/-- The partial Schubert inclusion is equivariant for the induced Levi action. -/
theorem partialSchubertLeviEquivariant (I J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w)
    (hdesc : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J)) :
    letI := partialSchubertLeviAction G I J w hw hdesc
    IsModHom (leviVariety G I).toOver (partialSchubertInclusion G J w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ (levi_stable G I J w hw hdesc)


end SchubertGeometry
