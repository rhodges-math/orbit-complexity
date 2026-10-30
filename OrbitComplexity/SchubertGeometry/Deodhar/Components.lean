import OrbitComplexity.SchubertGeometry.Deodhar.PrefixProjections
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.SchubertGeometry.Cells.Stability
import OrbitComplexity.GroupActions.Varieties.PointImageIso


/-! # Intrinsic Deodhar components

Regular projections to every prefix cell impose opposite-cell conditions. Their finite
intersection is locally closed and carries its reduced induced scheme structure.
The successor criterion separates the preceding component condition from the new cell condition.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2.
-/

open CategoryTheory AlgebraicGeometry Topology BruhatIntervals ReductiveGroups SchubertGeometry
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem locallyClosed_iInter {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (S : ι → Set X) (hS : ∀ i, IsLocallyClosed (S i)) :
    IsLocallyClosed (⋂ i, S i) := by
  classical
  have h : ∀ t : Finset ι, IsLocallyClosed (⋂ i ∈ t, S i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ] using
        isOpen_univ.isLocallyClosed (X := X)
    | @insert a t ha ih =>
      rw [Finset.set_biInter_insert]
      exact (hS a).inter ih
  simpa only [Finset.mem_univ, Set.iInter_true] using h Finset.univ

/-- The intrinsic support consists of flags with the prescribed opposite-cell prefixes. -/
def deodharPrefixSupport (n : ℕ) : Set (wordCell G word n).scheme :=
  ⋂ k : Fin (n + 1),
    (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val))).left ⁻¹'
        Set.range (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) k.val)).left

private theorem prefixSupport_locallyClosed (n : ℕ) :
    IsLocallyClosed (deodharPrefixSupport G expression hred n) := by
  apply locallyClosed_iInter
  intro k
  apply IsLocallyClosed.preimage _
    (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val))).left.continuous
  rw [GroupActions.orbitInclusion_range]
  exact GroupActions.orbitImage_locallyClosed _ _ _

/-- The reduced locally closed variety with the prescribed prefix conditions. -/
abbrev deodharPrefixComponent (n : ℕ) : GroupActions.Variety K :=
  (wordCell G word n).locallyClosedSubvariety (deodharPrefixSupport G expression hred n)
    (prefixSupport_locallyClosed G expression hred n)

/-- The intrinsic prefix component includes regularly into its ordinary prefix cell. -/
abbrev deodharPrefixInclusion (n : ℕ) :
    (deodharPrefixComponent G expression hred n).toOver ⟶ (wordCell G word n).toOver :=
  (wordCell G word n).locallyClosedInclusion (deodharPrefixSupport G expression hred n)
    (prefixSupport_locallyClosed G expression hred n)

/-- The scheme image of a prefix component is its intrinsic support. -/
theorem deodharPrefixInclusion_range (n : ℕ) :
    Set.range (deodharPrefixInclusion G expression hred n).left =
      deodharPrefixSupport G expression hred n :=
  GroupActions.Variety.locallyClosedInclusion_range _ _ _

omit [CharZero K] in
private theorem point_mem_range {A B : GroupActions.Variety K}
    (f : A.toOver ⟶ B.toOver) (x : B.points) :
    B.pointMap x ∈ Set.range f.left ↔ x ∈ Set.range (GroupActions.Variety.mapPoints f) := by
  constructor
  · exact GroupActions.Variety.exists_mapPoints_eq f x
  · rintro ⟨y, rfl⟩
    exact ⟨A.pointMap y, (GroupActions.Variety.pointMap_mapPoints f y).symm⟩

omit [CharZero K] in
private theorem preimage_point_mem_range {A B C : GroupActions.Variety K}
    (f : A.toOver ⟶ B.toOver) (i : C.toOver ⟶ B.toOver) (x : A.points) :
    f.left (A.pointMap x) ∈ Set.range i.left ↔
      GroupActions.Variety.mapPoints f x ∈ Set.range (GroupActions.Variety.mapPoints i) := by
  rw [← GroupActions.Variety.pointMap_mapPoints f x, point_mem_range]

/-- A rational point lies in the prefix component exactly when all prefix conditions hold. -/
theorem mem_deodharPrefix_points (n : ℕ) (x : (wordCell G word n).points) :
    x ∈ Set.range (GroupActions.Variety.mapPoints (deodharPrefixInclusion G expression hred n)) ↔
      ∀ k : Fin (n + 1), GroupActions.Variety.mapPoints
        (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
          schubertCellInclusion G
            (simpleWeylWord G.rootBase (word.take k.val))) x ∈
        Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) k.val))) := by
  rw [← point_mem_range, deodharPrefixInclusion_range]
  simp only [deodharPrefixSupport, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro k
  exact preimage_point_mem_range
    (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val)))
    (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k.val)) x

/-- The Deodhar component imposes the prefix conditions of the entire subexpression. -/
abbrev deodharComponent : GroupActions.Variety K :=
  deodharPrefixComponent G expression hred word.length

/-- The intrinsic Deodhar component includes regularly into the flag variety. -/
abbrev deodharInclusion :
    (deodharComponent G expression hred).toOver ⟶ (flagVariety G).toOver :=
  deodharPrefixInclusion G expression hred word.length ≫ schubertCellInclusion G
    (simpleWeylWord G.rootBase (word.take word.length))

end
end SchubertGeometry


open CategoryTheory AlgebraicGeometry Topology BruhatIntervals ReductiveGroups SchubertGeometry
namespace SchubertGeometry
noncomputable section

private theorem finite_conditions_succ {A B Y : Type*} (n : ℕ) (f : A → B)
    (p : Fin (n + 2) → A → Y) (q : Fin (n + 1) → B → Y) (top : A → Y)
    (S : ℕ → Set Y) (hp : ∀ k, p k.castSucc = q k ∘ f)
    (htop : p (Fin.last (n + 1)) = top) (x : A) :
    (∀ k, p k x ∈ S k.val) ↔
      (∀ k, q k (f x) ∈ S k.val) ∧ top x ∈ S (n + 1) := by
  constructor
  · intro h
    constructor
    · intro k
      have hk := h k.castSucc
      rwa [hp k] at hk
    · have hk := h (Fin.last (n + 1))
      rwa [htop] at hk
  · rintro ⟨h, ht⟩ k
    by_cases hk : k.val < n + 1
    · let j : Fin (n + 1) := ⟨k.val, hk⟩
      have he : k = j.castSucc := Fin.ext rfl
      change p k x ∈ S j.val
      rw [he, hp j]
      exact h j
    · have he : k = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      subst k
      rwa [htop]

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

omit [IsAlgClosed K] [CharZero K] in
private theorem points_assoc {A B C D : GroupActions.Variety K}
    (f : A.toOver ⟶ B.toOver) (g : B.toOver ⟶ C.toOver) (h : C.toOver ⟶ D.toOver)
    (x : A.points) :
    GroupActions.Variety.mapPoints ((f ≫ g) ≫ h) x =
      GroupActions.Variety.mapPoints (g ≫ h) (GroupActions.Variety.mapPoints f x) := by
  rw [Category.assoc, GroupActions.Variety.mapPoints_comp]

omit [IsAlgClosed K] [CharZero K] in
private theorem points_id_comp {A B : GroupActions.Variety K}
    (f : A.toOver ⟶ B.toOver) (x : A.points) :
    GroupActions.Variety.mapPoints (𝟙 A.toOver ≫ f) x = GroupActions.Variety.mapPoints f x :=
  congrArg (fun g : A.toOver ⟶ B.toOver => GroupActions.Variety.mapPoints g x)
    (Category.id_comp f)

/-- The next component condition is the preceding condition and its new opposite-cell condition. -/
theorem mem_deodharPrefix_succ (n : ℕ) (x : (wordCell G word (n + 1)).points) :
    x ∈ Set.range (GroupActions.Variety.mapPoints
      (deodharPrefixInclusion G expression hred (n + 1))) ↔
      GroupActions.Variety.mapPoints (wordCellStep G word hred n) x ∈
        Set.range (GroupActions.Variety.mapPoints (deodharPrefixInclusion G expression hred n)) ∧
      GroupActions.Variety.mapPoints
        (schubertCellInclusion G (simpleWeylWord G.rootBase
          (word.take (n + 1)))) x ∈
        Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
          (expression.prefixProd (weylCoxeterSystem G.rootBase) (n + 1)))) := by
  rw [mem_deodharPrefix_points, mem_deodharPrefix_points]
  refine finite_conditions_succ n
    (GroupActions.Variety.mapPoints (wordCellStep G word hred n))
    (fun k => GroupActions.Variety.mapPoints
      (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val))))
    (fun k => GroupActions.Variety.mapPoints
      (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val))))
    (GroupActions.Variety.mapPoints (schubertCellInclusion G
      (simpleWeylWord G.rootBase (word.take (n + 1)))))
    (fun k => Set.range (GroupActions.Variety.mapPoints (oppositeSchubertCellInclusion G
      (expression.prefixProd (weylCoxeterSystem G.rootBase) k)))) ?_ ?_ x
  · intro k
    funext y
    have hp := wordCellProjection_succ G word hred (Nat.le_of_lt_succ k.isLt)
    have hc := congrArg (fun f : (wordCell G word (n + 1)).toOver ⟶
        (wordCell G word k.val).toOver => GroupActions.Variety.mapPoints
      (f ≫ schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take k.val))) y) hp
    exact hc.trans (points_assoc (wordCellStep G word hred n)
      (wordCellProjection G word hred (Nat.le_of_lt_succ k.isLt))
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k.val))) y)
  · funext y
    have hp := wordCellProjection_self G word hred (n + 1)
    have hc := congrArg (fun f : (wordCell G word (n + 1)).toOver ⟶
        (wordCell G word (n + 1)).toOver => GroupActions.Variety.mapPoints
      (f ≫ schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take (n + 1)))) y) hp
    exact hc.trans (points_id_comp (schubertCellInclusion G
      (simpleWeylWord G.rootBase (word.take (n + 1)))) y)

end
end SchubertGeometry
