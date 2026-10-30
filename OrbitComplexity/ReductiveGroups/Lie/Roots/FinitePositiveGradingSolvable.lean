import OrbitComplexity.ReductiveGroups.Lie.Roots.HeightFilteredSolvable

/-!
# Finite Positive Grading Solvable

Finite positive gradings force solvability by a height filtration. -/

noncomputable section
namespace ReductiveGroups

variable {K B ι : Type*} [CommRing K] [LieRing B] [LieAlgebra K B]

/-- The submodule spanned by the homogeneous components `V i` of degree at least `n`. -/
def positiveGradingAbove (V : ι → Submodule K B) (degree : ι → ℕ) (n : ℕ) :
    Submodule K B :=
  ⨆ i, ⨆ (_ : n ≤ degree i), V i

/-- A Lie algebra spanned by finitely many strictly positive homogeneous
components is solvable when brackets have the sum degree. -/
theorem isSolvable_of_finite_positive_grading
    (V : ι → Submodule K B) (degree : ι → ℕ)
    (htop : (⨆ i, V i) = ⊤)
    (hpos : ∀ i, 0 < degree i)
    (hbracket : ∀ i j (x y : B), x ∈ V i → y ∈ V j →
      ⁅x, y⁆ ∈ positiveGradingAbove V degree (degree i + degree j))
    (N : ℕ) (hbound : ∀ i, degree i < N) : LieAlgebra.IsSolvable B := by
  let G := positiveGradingAbove V degree
  have hG_zero : G 0 = ⊤ := by
    simp [G, positiveGradingAbove, htop]
  have hG_terminal : G N = ⊥ := by
    simp only [G, positiveGradingAbove]
    refine iSup_eq_bot.mpr fun i => ?_
    rw [iSup_eq_bot]
    intro hi
    exact (False.elim ((not_le.mpr (hbound i)) hi))
  have hG_antitone {p q : ℕ} (hpq : p ≤ q) : G q ≤ G p := by
    intro x hx
    change x ∈ ⨆ i, ⨆ (_ : q ≤ degree i), V i at hx
    change x ∈ ⨆ i, ⨆ (_ : p ≤ degree i), V i
    have hle : (⨆ i, ⨆ (_ : q ≤ degree i), V i) ≤
        (⨆ i, ⨆ (_ : p ≤ degree i), V i) := by
      refine iSup₂_le (fun i hi => ?_)
      exact le_iSup₂_of_le i (hpq.trans hi) le_rfl
    exact hle hx
  have hG_bracket (p q : ℕ) (x y : B) (hx : x ∈ G p) (hy : y ∈ G q) :
      ⁅x, y⁆ ∈ G (p + q) := by
    have hpair (i j : ι) (hi : p ≤ degree i) (hj : q ≤ degree j)
        (x y : B) (hx : x ∈ V i) (hy : y ∈ V j) :
        ⁅x, y⁆ ∈ G (p + q) :=
      hG_antitone (Nat.add_le_add hi hj) (hbracket i j x y hx hy)
    change x ∈ ⨆ i, ⨆ (_ : p ≤ degree i), V i at hx
    suffices h : ∀ x ∈ ⨆ i, ⨆ (_ : p ≤ degree i), V i,
        ∀ y ∈ G q, ⁅x, y⁆ ∈ G (p + q) from h x hx y hy
    intro x hx
    refine Submodule.iSup_induction
      (motive := fun x => ∀ y ∈ G q, ⁅x, y⁆ ∈ G (p + q))
      _ hx ?_ ?_ ?_
    · intro i x hxi
      refine Submodule.iSup_induction
        (motive := fun x => ∀ y ∈ G q, ⁅x, y⁆ ∈ G (p + q))
        _ hxi ?_ ?_ ?_
      · intro hi x hxi y hy
        change y ∈ ⨆ j, ⨆ (_ : q ≤ degree j), V j at hy
        refine Submodule.iSup_induction
          (motive := fun y => ⁅x, y⁆ ∈ G (p + q))
          _ hy ?_ ?_ ?_
        · intro j y hyj
          refine Submodule.iSup_induction
            (motive := fun y => ⁅x, y⁆ ∈ G (p + q))
            _ hyj ?_ ?_ ?_
          · intro hj y hyj
            exact hpair i j hi hj x y hxi hyj
          · simp
          · intro y₁ y₂ hy₁ hy₂
            simpa only [lie_add] using add_mem hy₁ hy₂
        · simp
        · intro y₁ y₂ hy₁ hy₂
          simpa only [lie_add] using add_mem hy₁ hy₂
      · simp
      · intro x₁ x₂ hx₁ hx₂ y hy
        simpa only [add_lie] using add_mem (hx₁ y hy) (hx₂ y hy)
    · simp
    · intro x₁ x₂ hx₁ hx₂ y hy
      simpa only [add_lie] using add_mem (hx₁ y hy) (hx₂ y hy)
  have hG_one : G 1 = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun i => ?_
    exact le_iSup₂_of_le i (hpos i) le_rfl
  let F : ℕ → LieIdeal K B := fun n =>
    { G (n + 1) with
      lie_mem := by
        intro x y hy
        have hx : x ∈ G 0 := by rw [hG_zero]; trivial
        simpa using hG_bracket 0 (n + 1) x y hx hy }
  have hfirst : LieAlgebra.derivedSeries K B 1 ≤ F 0 := by
    change LieAlgebra.derivedSeries K B 1 ≤ G 1
    rw [hG_one]
    exact le_top
  have hraise (n : ℕ) : ⁅F n, F n⁆ ≤ F (n + 1) := by
    rw [LieSubmodule.lie_le_iff]
    intro x hx y hy
    change x ∈ G (n + 1) at hx
    change y ∈ G (n + 1) at hy
    change ⁅x, y⁆ ∈ G (n + 1 + 1)
    exact hG_antitone (by omega : n + 1 + 1 ≤ (n + 1) + (n + 1))
      (hG_bracket (n + 1) (n + 1) x y hx hy)
  have hterminal : F N = ⊥ := by
    apply eq_bot_iff.mpr
    change G (N + 1) ≤ ⊥
    rw [← hG_terminal]
    exact hG_antitone (Nat.le_succ N)
  exact HeightFilteredSolvable.isSolvable_bracket_raising_filtration F hfirst hraise N hterminal

end ReductiveGroups
