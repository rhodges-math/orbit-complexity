import OrbitComplexity.SchubertGeometry.Parabolics.ClosedSubgroups
import OrbitComplexity.SchubertGeometry.Parabolics.LeviStability

/-! # Stabilizers of Schubert varieties

The full setwise stabilizer of a reduced Schubert variety is the standard parabolic
of its left descents. The closed-subgroup classification reduces the equality to
the rank-one stability criterion.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory ReductiveGroups GroupActions
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The subgroup of group points preserving the reduced Schubert variety. -/
def schubertStabilizer (w : G.weylGroup) : Subgroup G.points :=
  MulAction.stabilizer G.points ((flagVarietyPointsEquiv G) ⁻¹'
    Set.range (Variety.mapPoints (schubertInclusion G w)))

private theorem groupFlag_mem_closure (w : G.weylGroup) (g : G.points) :
    flagVarietyPointsEquiv G (flagProjection G g) ∈
        Set.range (Variety.mapPoints (schubertInclusion G w)) ↔
      g ∈ closure (subgroupDoubleCoset G.borelPoints (G.weylPoint w)) := by
  rw [schubertVariety_points_cells, bruhat_doubleCoset_closure]
  simp only [Set.mem_iUnion, schubertCell_points_range, mem_schubertOrbit_iff]

private theorem stabilizer_closure (w : G.weylGroup) :
    schubertStabilizer G w = MulAction.stabilizer G.points
      (closure (subgroupDoubleCoset G.borelPoints (G.weylPoint w))) := by
  have hpre : (flagProjection G) ⁻¹' ((flagVarietyPointsEquiv G) ⁻¹'
      Set.range (Variety.mapPoints (schubertInclusion G w))) =
        closure (subgroupDoubleCoset G.borelPoints (G.weylPoint w)) := by
    ext g
    exact groupFlag_mem_closure G w g
  rw [← hpre]
  exact (stabilizer_preimage_of_surjective (flagProjection G)
    (flagProjection_surjective G) (fun _ _ => rfl) _).symm

private theorem stable_iff_le (w : G.weylGroup) (H : Subgroup G.points) :
    (∀ g ∈ H, ∀ q : flagPoints G,
      flagVarietyPointsEquiv G q ∈ Set.range (Variety.mapPoints (schubertInclusion G w)) →
        flagVarietyPointsEquiv G (g • q) ∈
          Set.range (Variety.mapPoints (schubertInclusion G w))) ↔
      H ≤ schubertStabilizer G w := by
  rw [schubertStabilizer, MulAction.le_stabilizer_iff_smul_le]
  constructor
  · intro h g hg
    rintro _ ⟨q, hq, rfl⟩
    exact h g hg q hq
  · intro h g hg q hq
    exact h g hg ⟨q, hq, rfl⟩

private theorem borel_le_stabilizer (w : G.weylGroup) :
    G.borelPoints ≤ schubertStabilizer G w := by
  apply (stable_iff_le G w G.borelPoints).mp
  intro b hb q hq
  let bp := (borelPointsMulEquiv G).symm ⟨b, hb⟩
  have hp : (borelPointsMulEquiv G bp : G.points) = b :=
    congrArg Subtype.val ((borelPointsMulEquiv G).apply_symm_apply ⟨b, hb⟩)
  have hs := schubertVariety_stable G w bp hq
  rw [borelFlag_smul, hp] at hs
  exact hs

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

/-- The full Schubert stabilizer is the standard parabolic of its left descents. -/
theorem schubertStabilizer_eq (w : G.weylGroup) :
    schubertStabilizer G w = standardParabolicPoints G
      (BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) := by
  have hclosed : IsClosed (schubertStabilizer G w : Set G.points) := by
    rw [stabilizer_closure]
    exact isClosed_set_stabilizer G _ isClosed_closure
  have hB := borel_le_stabilizer G w
  let I : Set G.rootBase.support := {i | G.reflectionPoint i.val ∈ schubertStabilizer G w}
  have hclass : schubertStabilizer G w = standardParabolicPoints G I :=
    closed_borel_subgroup_eq G _ hclosed hB
  have hI : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w := by
    have hstable := (stable_iff_le G w (standardParabolicPoints G I)).mpr
      (by rw [← hclass])
    have hroots := (parabolic_schubert_stable_iff G I w).mp hstable
    intro i hi
    exact (leftDescent_iff G w i).mpr (hroots i hi)
  apply le_antisymm
  · rw [hclass]
    apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, hi, rfl⟩
    exact (le_sup_right : Subgroup.closure _ ≤ standardParabolicPoints G _)
      (Subgroup.subset_closure ⟨i, hI hi, rfl⟩)
  · apply (stable_iff_le G w _).mp
    apply (parabolic_schubert_stable_iff G _ w).mpr
    intro i hi
    exact (leftDescent_iff G w i).mp hi

/-- The full stabilizer equality gives every algebraic Levi restriction at left descents. -/
theorem schubert_stabilizer_levi (w : G.weylGroup) :
    (schubertStabilizer G w = standardParabolicPoints G
      (BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w)) ∧
      ∀ I : Set G.rootBase.support,
        I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w →
        ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
          letI := a
          IsModHom (leviVariety G I).toOver (schubertInclusion G w) := by
  refine ⟨schubertStabilizer_eq G w, ?_⟩
  intro I hI
  exact ⟨schubertLeviAction G I w hI, schubertLeviEquivariant G I w hI⟩

end SchubertGeometry
