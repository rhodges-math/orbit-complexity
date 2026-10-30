import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSupportStability
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviRootClosed
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.LongestCount

/-! # Longest elements of standard parabolic subgroups

An inversion-count maximum exists in each finite standard parabolic subgroup. Its left
inversions are exactly the positive roots of the Levi subsystem. This characterizes the
element, determines its length, and shows that it is an involution. The longest left factor
is detected by the prescribed simple left descents.

## Main definitions and results

* `longestParabolicElement`: the longest element of a standard parabolic subgroup.
* `parabolic_inversions_subset`: inversion containment in the positive Levi roots.
* `leftRootInv_longestParabolic`: the full Levi inversion set.
* `rootCount_longestParabolic`: the cardinality of that inversion set.
* `longestParabolicElement_sq`: the longest element is an involution.
* `leftFactor_longest_iff`: the residual-root and left-descent criteria.
-/
noncomputable section
namespace ReductiveGroups
variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem]

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private theorem root_coefficient_cast (b : P.Base) (β : ι) (i : b.support) :
    simpleRootCoeff b i (P.root β) = (simpleRootCoeffInt b β i : K) := by
  classical
  obtain ⟨f, _, _, hf⟩ := b.exists_root_eq_sum_int β
  have hr : P.root β = ∑ j : b.support, f (j : ι) • P.root (j : ι) := by
    simpa only [b.support.sum_subtype (p := (· ∈ b.support))
      (by simp) (F := inferInstance)] using hf
  have hs : P.rootSpanMem ℤ β = ∑ j : b.support, f (j : ι) • b.toWeightBasisInt j := by
    apply Subtype.ext
    simpa using hr
  have hi : simpleRootCoeffInt b β i = f i := by
    rw [simpleRootCoeffInt, hs]
    simp [Finsupp.single_apply]
  have hrK : P.root β = ∑ j : b.support, (f (j : ι) : K) • b.toWeightBasis j := by
    simpa only [RootPairing.Base.toWeightBasis_apply, Int.cast_smul_eq_zsmul] using hr
  rw [hi]
  change b.toWeightBasis.repr (P.root β) i = (f (i : ι) : K)
  rw [hrK, map_sum]
  simp [Finsupp.single_apply]

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private theorem levi_iff_support (b : P.Base) (I : Set b.support) (β : ι) :
    β ∈ leviPositiveRoots b I ↔ b.IsPos β ∧ simpleRootSupportInt b β ⊆ I := by
  have hrange : Set.range (fun j : I => P.root j.val.val) = b.toWeightBasis '' I := by
    ext v
    simp [RootPairing.Base.toWeightBasis_apply]
  rw [leviPositiveRoots_eq_span, Set.mem_ofPred_eq, hrange, Module.Basis.mem_span_image]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hs i hi
    apply hs
    apply Finsupp.mem_support_iff.mpr
    change simpleRootCoeff b i (P.root β) ≠ 0
    rw [root_coefficient_cast]
    exact_mod_cast hi
  · intro hs i hi
    apply hs
    change simpleRootCoeffInt b β i ≠ 0
    have hn : simpleRootCoeff b i (P.root β) ≠ 0 := Finsupp.mem_support_iff.mp hi
    rw [root_coefficient_cast] at hn
    exact_mod_cast hn

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] in
private theorem negative_coefficient (b : P.Base) (β : ι) (hβ : ¬ b.IsPos β)
    (i : b.support) : simpleRootCoeffInt b β i ≤ 0 := by
  have hp := simpleRootCoeffInt_nonneg_of_isPos b
    (P.reflectionPerm β β) ((isPos_neg_index_iff b β).mpr hβ) i
  rw [simpleRootCoeffInt_neg_index] at hp
  omega

/-- Every left inversion of a standard parabolic element is a positive Levi root. -/
theorem parabolic_inversions_subset (b : P.Base) (I : Set b.support)
    (w : P.weylGroup) (hw : w ∈ standardParabolicSubgroup b I) :
    leftRootInversionIndices b w ⊆ leviPositiveRoots b I := by
  intro β hβ
  obtain ⟨hp, hn⟩ := (mem_leftRootInversionIndices b w β).mp hβ
  apply (levi_iff_support b I β).mpr
  refine ⟨hp, ?_⟩
  intro i hi
  by_contra hiI
  obtain ⟨word, hword, hprod⟩ := (mem_standardParabolicSubgroup_iff_word b I w⁻¹).mp
    ((standardParabolicSubgroup b I).inv_mem hw)
  have hin : i ∉ word := fun hx => hiI (hword i hx)
  have hcoeff := simpleRootCoeff_word_of_notMem b word hin (P.root β)
  rw [← simpleWeylWord_smul, hprod, P.weylGroup_apply_root] at hcoeff
  rw [root_coefficient_cast, root_coefficient_cast] at hcoeff
  have heq : simpleRootCoeffInt b (P.weylGroupToPerm w⁻¹ β) i =
      simpleRootCoeffInt b β i := by exact_mod_cast hcoeff
  have hpos := simpleRootCoeffInt_nonneg_of_isPos b β hp i
  have hneg := negative_coefficient b _ hn i
  rw [heq] at hneg
  exact hi (le_antisymm hneg hpos)

omit [P.IsRootSystem] in
private theorem exists_max (b : P.Base) (I : Set b.support) :
    ∃ w : standardParabolicSubgroup b I, ∀ v : standardParabolicSubgroup b I,
      rootInversionCount b v ≤ rootInversionCount b w := by
  let := weylGroup_finite b
  exact Finite.exists_max (fun w : standardParabolicSubgroup b I => rootInversionCount b w)

/-- The standard parabolic element maximizing the number of its left root inversions. -/
def longestParabolicElement (b : P.Base) (I : Set b.support) : P.weylGroup :=
  (Classical.choose (exists_max b I)).val

omit [P.IsRootSystem] in
/-- The longest parabolic element belongs to its prescribed standard parabolic subgroup. -/
theorem longestParabolicElement_mem (b : P.Base) (I : Set b.support) :
    longestParabolicElement b I ∈ standardParabolicSubgroup b I :=
  (Classical.choose (exists_max b I)).property

omit [P.IsRootSystem] in
/-- The longest parabolic element bounds inversion counts in its subgroup. -/
theorem longestParabolicElement_max (b : P.Base) (I : Set b.support) (v : P.weylGroup)
    (hv : v ∈ standardParabolicSubgroup b I) :
    rootInversionCount b v ≤ rootInversionCount b (longestParabolicElement b I) :=
  Classical.choose_spec (exists_max b I) ⟨v, hv⟩

omit [P.IsRootSystem] in
private theorem max_simple_neg (b : P.Base) (I : Set b.support) (w : P.weylGroup)
    (hw : w ∈ standardParabolicSubgroup b I)
    (hmax : ∀ v ∈ standardParabolicSubgroup b I, rootInversionCount b v ≤ rootInversionCount b w)
    (i : b.support) (hi : i ∈ I) : ¬ b.IsPos (P.weylGroupToPerm w i) := by
  intro hp
  have hinc := rootInversionCount_mul_simple_of_pos b w i hp
  have hbound := hmax (w * RootPairing.weylGroup.ofIdx P i)
    ((standardParabolicSubgroup b I).mul_mem hw (simple_mem_standardParabolicSubgroup b I i hi))
  omega

omit [P.IsRootSystem] in
private theorem negative_supported (b : P.Base) (I : Set b.support) (w : P.weylGroup)
    (hw : ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm w i)) (β : ι)
    (hp : b.IsPos β) (hs : simpleRootSupportInt b β ⊆ I) :
    ¬ b.IsPos (P.weylGroupToPerm w β) := by
  have hpos := isPos_weyl_image_of_simple_support b (longestWeylElement b * w) I
    (fun i hi => by
      simpa only [map_mul, Equiv.Perm.mul_apply, longestWeylElement_isPos_iff] using hw i hi)
    β hp hs
  apply (longestWeylElement_isPos_iff b (P.weylGroupToPerm w β)).mp
  simpa only [map_mul, Equiv.Perm.mul_apply] using hpos

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] in
private theorem neg_support (b : P.Base) (β : ι) :
    simpleRootSupportInt b (P.reflectionPerm β β) = simpleRootSupportInt b β := by
  ext i
  simp only [simpleRootSupportInt, Set.mem_ofPred_eq, simpleRootCoeffInt_neg_index, neg_ne_zero]

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] in
private theorem simple_supported (b : P.Base) (I : Set b.support)
    (i : b.support) (hi : i ∈ I) : simpleRootSupportInt b i ⊆ I := by
  intro j hj
  by_contra hjI
  have hne : i ≠ j := fun h => hjI (h ▸ hi)
  change simpleRootCoeffInt b (i : ι) j ≠ 0 at hj
  exact hj (by simp only [simpleRootCoeffInt_simple, ite_eq_right hne])

private theorem eq_of_simple_neg (b : P.Base) (I : Set b.support) (u v : P.weylGroup)
    (hu : u ∈ standardParabolicSubgroup b I) (hv : v ∈ standardParabolicSubgroup b I)
    (hun : ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm u i))
    (hvn : ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm v⁻¹ i)) : v = u := by
  let r := u⁻¹ * v
  have hrI : r ∈ standardParabolicSubgroup b I :=
    (standardParabolicSubgroup b I).mul_mem ((standardParabolicSubgroup b I).inv_mem hu) hv
  have hempty : leftRootInversionIndices b r = ∅ := by
    ext γ
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hγ
    have hγI := (levi_iff_support b I γ).mp (parabolic_inversions_subset b I r hrI hγ)
    have hγneg := negative_supported b I u hun γ hγI.1 hγI.2
    let α := P.weylGroupToPerm u γ
    let δ := P.reflectionPerm α α
    have hδpos : b.IsPos δ := (isPos_neg_index_iff b α).mpr hγneg
    have hδsupp : simpleRootSupportInt b δ ⊆ I := by
      change simpleRootSupportInt b (P.reflectionPerm α α) ⊆ I
      rw [neg_support]
      exact standardParabolic_preserves_root_support b I u hu γ hγI.2
    have hδneg := negative_supported b I v⁻¹ hvn δ hδpos hδsupp
    change ¬ b.IsPos (P.weylGroupToPerm v⁻¹ (P.reflectionPerm α α)) at hδneg
    rw [weylGroupToPerm_neg_index, isPos_neg_index_iff] at hδneg
    have hpos := not_not.mp hδneg
    apply ((mem_leftRootInversionIndices b r γ).mp hγ).2
    simpa only [r, mul_inv_rev, inv_inv, map_mul, Equiv.Perm.mul_apply, α] using hpos
  have hr : r = 1 := (rootInversionCount_eq_zero_iff b r).mp
    (by simp only [rootInversionCount, leftRootInversions, hempty,
      Set.image_empty, Set.ncard_empty])
  change u⁻¹ * v = 1 at hr
  exact (inv_mul_eq_one.mp hr).symm

omit [P.IsRootSystem] in
private theorem longest_right_neg (b : P.Base) (I : Set b.support) :
    ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm (longestParabolicElement b I) i) :=
  max_simple_neg b I _ (longestParabolicElement_mem b I) (longestParabolicElement_max b I)

omit [P.IsRootSystem] in
private theorem longest_left_neg (b : P.Base) (I : Set b.support) :
    ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm (longestParabolicElement b I)⁻¹ i) :=
  max_simple_neg b I _ ((standardParabolicSubgroup b I).inv_mem (longestParabolicElement_mem b I))
    (fun v hv => by simpa only [rootInversionCount_inv] using longestParabolicElement_max b I v hv)

/-- A parabolic element is longest exactly when all prescribed simples are left descents. -/
theorem eq_longestParabolic_iff (b : P.Base) (I : Set b.support) (v : P.weylGroup)
    (hv : v ∈ standardParabolicSubgroup b I) :
    v = longestParabolicElement b I ↔ ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm v⁻¹ i) := by
  constructor
  · rintro rfl
    exact longest_left_neg b I
  · exact eq_of_simple_neg b I _ v (longestParabolicElement_mem b I) hv (longest_right_neg b I)

/-- The longest parabolic element inverts exactly the positive roots of its Levi subsystem. -/
theorem leftRootInv_longestParabolic (b : P.Base) (I : Set b.support) :
    leftRootInversionIndices b (longestParabolicElement b I) = leviPositiveRoots b I := by
  apply Set.Subset.antisymm (parabolic_inversions_subset b I _ (longestParabolicElement_mem b I))
  intro β hβ
  obtain ⟨hp, hs⟩ := (levi_iff_support b I β).mp hβ
  exact (mem_leftRootInversionIndices b _ β).mpr
    ⟨hp, negative_supported b I _ (longest_left_neg b I) β hp hs⟩

/-- The longest parabolic element has one inversion for every positive Levi root. -/
theorem rootCount_longestParabolic (b : P.Base) (I : Set b.support) :
    rootInversionCount b (longestParabolicElement b I) =
      Nat.card {r // r ∈ leviPositiveRoots b I} := by
  rw [rootInversionCount, leftRootInversions, leftRootInv_longestParabolic]
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_image_of_injective _ P.root.injective

/-- The longest parabolic element is an involution. -/
theorem longestParabolicElement_sq (b : P.Base) (I : Set b.support) :
    longestParabolicElement b I * longestParabolicElement b I = 1 := by
  have hinv : (longestParabolicElement b I)⁻¹ = longestParabolicElement b I :=
    (eq_longestParabolic_iff b I _ ((standardParabolicSubgroup b I).inv_mem
      (longestParabolicElement_mem b I))).mpr (by simpa only [inv_inv] using longest_right_neg b I)
  calc
    _ = longestParabolicElement b I * (longestParabolicElement b I)⁻¹ :=
      congrArg (fun v => longestParabolicElement b I * v) hinv.symm
    _ = 1 := mul_inv_cancel _

/-- The longest parabolic element is the unique inversion-count maximizer in its subgroup. -/
theorem eq_longestParabolic_of_max (b : P.Base) (I : Set b.support) (v : P.weylGroup)
    (hv : v ∈ standardParabolicSubgroup b I)
    (hmax : ∀ a ∈ standardParabolicSubgroup b I, rootInversionCount b a ≤ rootInversionCount b v) :
    v = longestParabolicElement b I := by
  apply (eq_longestParabolic_iff b I v hv).mpr
  exact max_simple_neg b I v⁻¹ ((standardParabolicSubgroup b I).inv_mem hv)
    (fun a ha => by simpa only [rootInversionCount_inv] using hmax a ha)

/-- A parabolic element is longest exactly when it leaves no positive Levi root uninverted. -/
theorem eq_longestParabolic_iff_empty (b : P.Base) (I : Set b.support) (v : P.weylGroup)
    (hv : v ∈ standardParabolicSubgroup b I) :
    v = longestParabolicElement b I ↔ leviPositiveRoots b I \ leftRootInversionIndices b v = ∅ := by
  constructor
  · rintro rfl
    rw [leftRootInv_longestParabolic, Set.sdiff_self]
  · intro he
    apply (eq_longestParabolic_iff b I v hv).mpr
    intro i hi
    have hroot : (i : ι) ∈ leviPositiveRoots b I :=
      (levi_iff_support b I i).mpr ⟨b.isPos_of_mem_support i.property, simple_supported b I i hi⟩
    exact ((mem_leftRootInversionIndices b v i).mp ((Set.sdiff_eq_empty.mp he) hroot)).2

omit [P.IsRootSystem] in
private theorem minimal_preserves_sign (b : P.Base) (I : Set b.support) (d : P.weylGroup)
    (hd : IsMinimalLeftParabolic b I d) (β : ι) (hs : simpleRootSupportInt b β ⊆ I) :
    b.IsPos (P.weylGroupToPerm d⁻¹ β) ↔ b.IsPos β := by
  constructor
  · intro hp
    by_contra hn
    have hneg := MinimalLeftParabolic.preserves_supported_positive_root b I d hd
      (P.reflectionPerm β β) ((isPos_neg_index_iff b β).mpr hn) (by rwa [neg_support])
    rw [weylGroupToPerm_neg_index, isPos_neg_index_iff] at hneg
    exact hneg hp
  · intro hp
    exact MinimalLeftParabolic.preserves_supported_positive_root b I d hd β hp hs

omit [P.IsRootSystem] in
private theorem factor_left_sign (b : P.Base) (I : Set b.support) (w : P.weylGroup)
    (i : b.support) (hi : i ∈ I) :
    b.IsPos (P.weylGroupToPerm w⁻¹ i) ↔
      b.IsPos (P.weylGroupToPerm (leftParabolicFactor b I w)⁻¹ i) := by
  have hs := standardParabolic_preserves_root_support b I (leftParabolicFactor b I w)⁻¹
    ((standardParabolicSubgroup b I).inv_mem (leftParabolicFactor_mem b I w)) i
    (simple_supported b I i hi)
  have hf := congrArg (fun v : P.weylGroup => P.weylGroupToPerm v⁻¹ i)
    (leftParabolic_factorization b I w)
  simp only [mul_inv_rev, map_mul, Equiv.Perm.mul_apply] at hf
  rw [hf]
  exact minimal_preserves_sign b I _ (leftParabolicRepresentative_minimal b I w) _ hs

/-- The longest left factor is detected by an empty residual Levi set and all left descents. -/
theorem leftFactor_longest_iff (b : P.Base) (I : Set b.support) (w : P.weylGroup) :
    (leftParabolicFactor b I w = longestParabolicElement b I ↔
      leviPositiveRoots b I \ leftRootInversionIndices b (leftParabolicFactor b I w) = ∅) ∧
    (leftParabolicFactor b I w = longestParabolicElement b I ↔
      ∀ i ∈ I, ¬ b.IsPos (P.weylGroupToPerm w⁻¹ i)) := by
  refine ⟨eq_longestParabolic_iff_empty b I _ (leftParabolicFactor_mem b I w), ?_⟩
  rw [eq_longestParabolic_iff b I _ (leftParabolicFactor_mem b I w)]
  constructor
  · intro ha i hi hp
    exact ha i hi ((factor_left_sign b I w i hi).mp hp)
  · intro hw i hi hp
    exact hw i hi ((factor_left_sign b I w i hi).mpr hp)

end ReductiveGroups