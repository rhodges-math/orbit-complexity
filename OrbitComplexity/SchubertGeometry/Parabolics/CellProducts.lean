import OrbitComplexity.SchubertGeometry.Parabolics.DoubleCosets

/-! # Minimal parabolic Bruhat cell products

A minimal right representative and a parabolic Weyl element give an exact product
of Bruhat double cosets. Reduced parabolic words remain ascending after the minimal
representative, so repeated rank-one multiplication yields the product formula.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem cell_one : subgroupDoubleCoset G.borelPoints (G.weylPoint 1) =
    (G.borelPoints : Set G.points) := by
  rw [G.weylPoint_eq, weylElementPoint_one]
  ext g
  constructor
  · rintro ⟨b, hb, c, hc, rfl⟩
    change b * 1 * c ∈ G.borelPoints
    simpa only [mul_one] using G.borelPoints.mul_mem hb hc
  · intro hg
    exact ⟨g, hg, 1, G.borelPoints.one_mem, by simp⟩

private theorem simple_mul_eq (w : G.weylGroup) (i : G.rootBase.support)
    (hp : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i)) :
    subgroupDoubleCoset G.borelPoints (G.weylPoint w) *
      subgroupDoubleCoset G.borelPoints
        (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) =
      subgroupDoubleCoset G.borelPoints
        (G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  simpa only [G.weylPoint_eq] using G.isBruhatSystem.doubleCoset_mul_eq_of_isPos w i hp

private theorem multiply_word (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) : ∀ l : List G.rootBase.support,
    (∀ i ∈ l, i ∈ J) →
    rootInversionCount G.rootBase (simpleWeylWord G.rootBase l) = l.length →
      subgroupDoubleCoset G.borelPoints (G.weylPoint w) *
        subgroupDoubleCoset G.borelPoints (G.weylPoint (simpleWeylWord G.rootBase l)) =
      subgroupDoubleCoset G.borelPoints (G.weylPoint (w * simpleWeylWord G.rootBase l)) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _ _
    rw [show simpleWeylWord G.rootBase [] = (1 : G.weylGroup) from rfl,
      cell_one, mul_one, subgroupDoubleCoset_mul_subgroup]
  | append_singleton l i ih =>
    intro hl hred
    have hl' : ∀ j ∈ l, j ∈ J := fun j hj => hl j (List.mem_append_left _ hj)
    have hi : i ∈ J := hl i (by simp)
    have hred' := RootInversionCount.prefix_of_reduced_append_singleton G.rootBase l i hred
    have hp := isPos_of_reduced_append G.rootBase l i hred
    have hlength : rootInversionCount G.rootBase
        (simpleWeylWord G.rootBase l * RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
          l.length + 1 := by
      simpa only [simpleWeylWord_append_singleton, List.length_append,
        List.length_singleton] using hred
    have hwp := isPos_parabolic_prefix_of_minimal_right G.rootBase J w hw l hl' i hi hlength
    have hstep := simple_mul_eq G (simpleWeylWord G.rootBase l) i hp
    have hwstep := simple_mul_eq G (w * simpleWeylWord G.rootBase l) i hwp
    let D (v : G.weylGroup) : Set G.points :=
      subgroupDoubleCoset G.borelPoints (G.weylPoint v)
    have hword := simpleWeylWord_append_singleton G.rootBase l i
    have hfactor : D (simpleWeylWord G.rootBase (l ++ [i])) =
        D (simpleWeylWord G.rootBase l) *
          D (RootPairing.weylGroup.ofIdx G.rootSystem i.val) :=
      (congrArg D hword).trans hstep.symm
    have hproduct : (w * simpleWeylWord G.rootBase l) *
        RootPairing.weylGroup.ofIdx G.rootSystem i.val =
          w * simpleWeylWord G.rootBase (l ++ [i]) :=
      (mul_assoc w (simpleWeylWord G.rootBase l)
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).trans
          (congrArg (fun v : G.weylGroup => w * v) hword.symm)
    change D w * D (simpleWeylWord G.rootBase (l ++ [i])) =
      D (w * simpleWeylWord G.rootBase (l ++ [i]))
    calc
      _ = D w * (D (simpleWeylWord G.rootBase l) *
          D (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :=
        congrArg (fun A : Set G.points => D w * A) hfactor
      _ = (D w * D (simpleWeylWord G.rootBase l)) *
          D (RootPairing.weylGroup.ofIdx G.rootSystem i.val) := (mul_assoc _ _ _).symm
      _ = D (w * simpleWeylWord G.rootBase l) *
          D (RootPairing.weylGroup.ofIdx G.rootSystem i.val) :=
        congrArg (fun A : Set G.points =>
          A * D (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) (ih hl' hred')
      _ = D ((w * simpleWeylWord G.rootBase l) *
          RootPairing.weylGroup.ofIdx G.rootSystem i.val) := hwstep
      _ = D (w * simpleWeylWord G.rootBase (l ++ [i])) := congrArg D hproduct

/-- Bruhat double cosets multiply exactly across a minimal right parabolic factorization. -/
theorem minimal_parabolic_cell_mul (J : Set G.rootBase.support) (w a : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w)
    (ha : a ∈ standardParabolicSubgroup G.rootBase J) :
    subgroupDoubleCoset G.borelPoints (G.weylPoint w) *
      subgroupDoubleCoset G.borelPoints (G.weylPoint a) =
        subgroupDoubleCoset G.borelPoints (G.weylPoint (w * a)) := by
  obtain ⟨l, hl, hprod, hlen⟩ := exists_reduced_standardParabolic_word G.rootBase J a ha
  have hred : rootInversionCount G.rootBase (simpleWeylWord G.rootBase l) = l.length := by
    rw [hprod, hlen]
  simpa only [hprod] using multiply_word G J w hw l hl hred

end SchubertGeometry
