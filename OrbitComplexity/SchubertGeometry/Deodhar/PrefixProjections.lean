import OrbitComplexity.SchubertGeometry.Deodhar.PartialProjection

/-! # Regular prefix projections on a reduced word

Each increasing simple extension has a regular cell projection. Composing these maps gives
the projections from a Schubert cell to all preceding cells of the chosen reduced word.
-/

open CategoryTheory ReductiveGroups CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
private def composeDown {C : Type*} [Category C] (X : ℕ → C)
    (p : ∀ n, X (n + 1) ⟶ X n) {i j : ℕ} (h : i ≤ j) : X j ⟶ X i :=
  Nat.leRecOn h (@fun n f => p n ≫ f) (𝟙 (X i))

private theorem composeDown_self {C : Type*} [Category C] (X : ℕ → C)
    (p : ∀ n, X (n + 1) ⟶ X n) (i : ℕ) :
    composeDown X p (Nat.le_refl i) = 𝟙 (X i) := by
  exact Nat.leRecOn_self _

private theorem composeDown_succ {C : Type*} [Category C] (X : ℕ → C)
    (p : ∀ n, X (n + 1) ⟶ X n) {i j : ℕ} (h : i ≤ j) :
    composeDown X p (h.trans (Nat.le_succ j)) = p j ≫ composeDown X p h := by
  exact Nat.leRecOn_succ h _

private theorem composeDown_trans {C : Type*} [Category C] (X : ℕ → C)
    (p : ∀ n, X (n + 1) ⟶ X n) {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k) :
    composeDown X p (h.trans h') = composeDown X p h' ≫ composeDown X p h := by
  induction k, h' using Nat.le_induction with
  | base => rw [composeDown_self, Category.id_comp]
  | succ k hk ih =>
    rw [composeDown_succ X p (h.trans hk), composeDown_succ X p hk, ih, Category.assoc]

section Words
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Fintype ι] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (word : List b.support)

omit [CharZero R] [Fintype ι] [P.IsCrystallographic] [P.IsReduced] in
private theorem prefix_next (n : ℕ) (hn : n < word.length) :
    simpleWeylWord b (word.take (n + 1)) =
      simpleWeylWord b (word.take n) *
        RootPairing.weylGroup.ofIdx P word[n] := by
  rw [List.take_succ_eq_append_getElem hn, simpleWeylWord_append]
  simp only [simpleWeylWord, mul_one]

private theorem prefix_ascent (hred : (weylCoxeterSystem b).IsReduced word)
    (n : ℕ) (hn : n < word.length) :
    b.IsPos (P.weylGroupToPerm (simpleWeylWord b (word.take n)) word[n]) := by
  apply isPos_of_length_mul_simple b _ word[n]
  have hs := (hred.take (n + 1)).eq
  have hp := (hred.take n).eq
  rw [weylCoxeterSystem_wordProd] at hs hp
  rw [prefix_next b word n hn, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hn)] at hs
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at hp
  exact hs.trans (congrArg (fun k => k + 1) hp.symm)
end Words

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

/-- The Schubert cell of a prefix of a word in simple reflections. -/
abbrev wordCell (n : ℕ) : GroupActions.Variety K :=
  schubertCell G (simpleWeylWord G.rootBase (word.take n))

private theorem prefix_stable (n : ℕ) (hn : ¬n < word.length) :
    simpleWeylWord G.rootBase (word.take (n + 1)) =
      simpleWeylWord G.rootBase (word.take n) := by
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- Appending the next letter identifies the product-index cell with the next prefix cell. -/
def wordCellExtensionIso (n : ℕ) (hn : n < word.length) :
    (schubertCell G (simpleWeylWord G.rootBase (word.take n) *
      RootPairing.weylGroup.ofIdx G.rootSystem word[n])).toOver ≅
        (wordCell G word (n + 1)).toOver :=
  eqToIso (congrArg (fun w : G.weylGroup => (schubertCell G w).toOver)
    (prefix_next G.rootBase word n hn).symm)

/-- The regular cell projection removing the next letter of a reduced word. -/
def wordCellStep (n : ℕ) :
    (wordCell G word (n + 1)).toOver ⟶ (wordCell G word n).toOver := by
  classical
  by_cases hn : n < word.length
  · exact eqToHom (congrArg (fun w : G.weylGroup => (schubertCell G w).toOver)
      (prefix_next G.rootBase word n hn)) ≫
      rankOneCellProjection G (simpleWeylWord G.rootBase (word.take n))
        word[n] (prefix_ascent G.rootBase word hred n hn)
  · exact eqToHom (congrArg (fun w : G.weylGroup => (schubertCell G w).toOver)
      (prefix_stable G word n hn))

/-- The intrinsic prefix projection is the increasing simple-extension projection. -/
theorem wordCellStep_eq (n : ℕ) (hn : n < word.length)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (simpleWeylWord G.rootBase (word.take n)) word[n])) :
    wordCellStep G word hred n =
      (wordCellExtensionIso G word n hn).inv ≫
        rankOneCellProjection G (simpleWeylWord G.rootBase (word.take n)) word[n] hi := by
  simp only [wordCellStep, dite_eq_left hn, wordCellExtensionIso]
  rfl

/-- The regular projection between two nested prefixes of a reduced word. -/
def wordCellProjection {i j : ℕ} (h : i ≤ j) :
    (wordCell G word j).toOver ⟶ (wordCell G word i).toOver :=
  composeDown (fun n => (wordCell G word n).toOver) (wordCellStep G word hred) h

/-- Projection from a word prefix to itself is the identity. -/
theorem wordCellProjection_self (i : ℕ) :
    wordCellProjection G word hred (Nat.le_refl i) = 𝟙 _ :=
  composeDown_self _ _ i

/-- Removing the last letter precedes every shorter prefix projection. -/
theorem wordCellProjection_succ {i j : ℕ} (h : i ≤ j) :
    wordCellProjection G word hred (h.trans (Nat.le_succ j)) =
      wordCellStep G word hred j ≫ wordCellProjection G word hred h :=
  composeDown_succ _ _ h

/-- Regular prefix projections compose along nested prefixes. -/
theorem wordCellProjection_trans {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k) :
    wordCellProjection G word hred (h.trans h') =
      wordCellProjection G word hred h' ≫ wordCellProjection G word hred h :=
  composeDown_trans _ _ h h'

end
end SchubertGeometry
