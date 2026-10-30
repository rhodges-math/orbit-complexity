import OrbitComplexity.SchubertGeometry.Parabolics.CellStability
import OrbitComplexity.SchubertGeometry.Levi.Actions
import OrbitComplexity.SchubertGeometry.Levi.Center
import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.BruhatIntervals.Order.Descents
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviSimple

/-! # Levi actions on Schubert varieties

A standard Levi preserves a Schubert closure exactly when its prescribed simple roots
are left descents. Generation by the selected rank-one subgroups gives rational-point
stability, and the reduced closed subvariety inherits the algebraic action.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory ReductiveGroups GroupActions
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def schubertFlagSet (w : G.weylGroup) : Set (flagPoints G) :=
  (flagVarietyPointsEquiv G) ⁻¹' Set.range (Variety.mapPoints (schubertInclusion G w))

private theorem stable_iff_le (w : G.weylGroup) (H : Subgroup G.points) :
    (∀ g ∈ H, ∀ q : flagPoints G,
      flagVarietyPointsEquiv G q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
        flagVarietyPointsEquiv G (g • q) ∈
          Set.range (Variety.mapPoints (schubertInclusion G w))) ↔
      H ≤ MulAction.stabilizer G.points (schubertFlagSet G w) := by
  rw [MulAction.le_stabilizer_iff_smul_le]
  constructor
  · intro h g hg
    rintro _ ⟨q, hq, rfl⟩
    exact h g hg q hq
  · intro h g hg q hq
    exact h g hg ⟨q, hq, rfl⟩

private theorem borel_le_stabilizer (w : G.weylGroup) :
    G.borelPoints ≤ MulAction.stabilizer G.points (schubertFlagSet G w) := by
  apply (stable_iff_le G w G.borelPoints).mp
  intro b hb q hq
  let bp := (borelPointsMulEquiv G).symm ⟨b, hb⟩
  have hp : (borelPointsMulEquiv G bp : G.points) = b :=
    congrArg Subtype.val ((borelPointsMulEquiv G).apply_symm_apply ⟨b, hb⟩)
  have hs := schubertVariety_stable G w bp hq
  rw [borelFlag_smul, hp] at hs
  exact hs

private theorem levi_stability_points (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∀ l : (leviVariety G I).points, ∀ q : (flagVariety G).points,
      q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
        l • q ∈ Set.range (Variety.mapPoints (schubertInclusion G w))) ↔
      G.leviPoints I ≤ MulAction.stabilizer G.points (schubertFlagSet G w) := by
  rw [← stable_iff_le]
  constructor
  · intro h l hl q hq
    let lp := (leviPointsMulEquiv G I).symm ⟨l, hl⟩
    have hp : (leviPointsMulEquiv G I lp : G.points) = l :=
      congrArg Subtype.val ((leviPointsMulEquiv G I).apply_symm_apply ⟨l, hl⟩)
    have hs := h lp (flagVarietyPointsEquiv G q) hq
    rw [leviFlag_smul, flagVarietyAction_points, hp] at hs
    exact hs
  · intro h l q hq
    obtain ⟨p, rfl⟩ := (flagVarietyPointsEquiv G).surjective q
    rw [leviFlag_smul, flagVarietyAction_points]
    exact h _ (leviPointsMulEquiv G I l).property p hq

private theorem action_iff_stable (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
      ∀ l : (leviVariety G I).points, ∀ q : (flagVariety G).points,
        q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
          l • q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) := by
  constructor
  · rintro ⟨a, ha⟩
    let := a
    let : IsModHom (leviVariety G I).toOver (schubertInclusion G w) := ha
    rintro l q ⟨y, rfl⟩
    refine ⟨l • y, ?_⟩
    apply (flagVariety G).pointsEquivOverHom.injective
    change (schubertVariety G w).pointsEquivOverHom (l • y) ≫ schubertInclusion G w =
      (flagVariety G).pointsEquivOverHom
        (l • Variety.mapPoints (schubertInclusion G w) y)
    rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
    exact IsModHom.map_smul (schubertInclusion G w)
      ((leviVariety G I).pointsEquivOverHom l) ((schubertVariety G w).pointsEquivOverHom y)
  · intro hstable
    let act := Variety.modObjOfInvariant (leviVariety G I) (flagVariety G)
      (schubertVariety G w) (schubertInclusion G w)
        (fun l y => hstable l (Variety.mapPoints (schubertInclusion G w) y) ⟨y, rfl⟩)
    exact ⟨act, Variety.modObjOfInvariant_isModHom _ _ _ _
      (fun l y => hstable l (Variety.mapPoints (schubertInclusion G w) y) ⟨y, rfl⟩)⟩

private theorem leftDescent_iff (w : G.weylGroup) (i : G.rootBase.support) :
    (weylCoxeterSystem G.rootBase).IsLeftDescent w i ↔
      ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i.val) := by
  rw [← (weylCoxeterSystem G.rootBase).isRightDescent_inv_iff]
  simp only [CoxeterSystem.IsRightDescent, weylCoxeterSystem_simple, weylCoxeterSystem_length]
  by_cases hp : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i.val)
  · rw [rootInversionCount_mul_simple_of_pos G.rootBase w⁻¹ i hp]
    constructor
    · intro h
      omega
    · intro hn
      exact (hn hp).elim
  · have hdrop := rootInversionCount_mul_simple_of_neg G.rootBase w⁻¹ i
      ((root_height_neg_iff_not_isPos G.rootBase _).mpr hp)
    constructor
    · exact fun _ => hp
    · intro _
      omega

private theorem parabolic_le_levi_borel (I : Set G.rootBase.support) :
    standardParabolicPoints G I ≤ G.leviPoints I ⊔ G.borelPoints := by
  apply sup_le le_sup_right
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, hi, rfl⟩
  exact Subgroup.mem_sup_left (G.reflectionPoint_mem_levi I i hi)

private theorem descents_of_levi_stable (I : Set G.rootBase.support) (w : G.weylGroup)
    (hstable : ∀ l : (leviVariety G I).points, ∀ q : (flagVariety G).points,
      q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
        l • q ∈ Set.range (Variety.mapPoints (schubertInclusion G w))) :
    I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w := by
  have hL := (levi_stability_points G I w).mp hstable
  have hH := (parabolic_le_levi_borel G I).trans
    (sup_le hL (borel_le_stabilizer G w))
  have hpoints := (stable_iff_le G w (standardParabolicPoints G I)).mpr hH
  have hroots := (parabolic_schubert_stable_iff G I w).mp hpoints
  intro i hi
  exact (leftDescent_iff G w i).mpr (hroots i hi)

private theorem levi_stable_of_descents (I : Set G.rootBase.support) (w : G.weylGroup)
    (hdesc : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) :
    ∀ l : (leviVariety G I).points, ∀ q : (flagVariety G).points,
      q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
        l • q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) := by
  have hroots : ∀ i ∈ I,
      ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i.val) := by
    intro i hi
    exact (leftDescent_iff G w i).mp (hdesc hi)
  have hH := (stable_iff_le G w (standardParabolicPoints G I)).mp
    ((parabolic_schubert_stable_iff G I w).mpr hroots)
  have hL : G.leviPoints I ≤ standardParabolicPoints G I := by
    rw [standardParabolicPoints, ← levi_sup_borel_eq]
    exact le_sup_left
  exact (levi_stability_points G I w).mpr (hL.trans hH)

/-- Prescribed left descents give the inherited algebraic Levi action on the Schubert variety. -/
@[instance_reducible]
def schubertLeviAction (I : Set G.rootBase.support) (w : G.weylGroup)
    (hdesc : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) :
    ModObj (leviVariety G I).toOver (schubertVariety G w).toOver :=
  Variety.modObjOfInvariant (leviVariety G I) (flagVariety G) (schubertVariety G w)
    (schubertInclusion G w) (fun l y => levi_stable_of_descents G I w hdesc l
      (Variety.mapPoints (schubertInclusion G w) y) ⟨y, rfl⟩)

/-- The inherited Levi action makes the closed Schubert inclusion equivariant. -/
theorem schubertLeviEquivariant (I : Set G.rootBase.support) (w : G.weylGroup)
    (hdesc : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) :
    let := schubertLeviAction G I w hdesc
    IsModHom (leviVariety G I).toOver (schubertInclusion G w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ (fun l y =>
    levi_stable_of_descents G I w hdesc l
      (Variety.mapPoints (schubertInclusion G w) y) ⟨y, rfl⟩)

/-- An equivariant algebraic Levi restriction exists exactly at the prescribed left descents. -/
theorem levi_schubert_action_iff (I : Set G.rootBase.support) (w : G.weylGroup) :
    (∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
      I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w := by
  constructor
  · intro hact
    exact descents_of_levi_stable G I w ((action_iff_stable G I w).mp hact)
  · intro hdesc
    exact ⟨schubertLeviAction G I w hdesc, schubertLeviEquivariant G I w hdesc⟩

end SchubertGeometry
