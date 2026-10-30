import OrbitComplexity.SchubertGeometry.Deodhar.PrefixProjections

/-! # Chart identifications of reduced-word prefixes

Appending the next letter identifies its simple-extension cell with the next prefix cell.
This identification commutes with the flag inclusion and with the preceding-cell projection.
-/

open CategoryTheory ReductiveGroups
namespace SchubertGeometry
noncomputable section

private theorem familyMap_cast {C I : Type*} [Category C]
    (F : I → C) {Z : C} (f : ∀ i, F i ⟶ Z) {a b : I} (h : a = b) :
    (eqToIso (congrArg F h)).hom ≫ f b = f a := by
  subst b
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

private theorem iso_cancel {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (p : B ⟶ D) (q : A ⟶ D) (h : p = e.inv ≫ q) : e.hom ≫ p = q := by
  rw [h, Iso.hom_inv_id_assoc]

section Words
variable {idx R M N : Type*} [Field R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing idx R M N} (b : P.Base) (word : List b.support)

private theorem word_next (n : ℕ) (hn : n < word.length) :
    simpleWeylWord b (word.take (n + 1)) =
      simpleWeylWord b (word.take n) * RootPairing.weylGroup.ofIdx P word[n] := by
  rw [List.take_succ_eq_append_getElem hn, simpleWeylWord_append]
  simp only [simpleWeylWord, mul_one]
end Words

section Signs
variable {idx R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing idx R M N} [Fintype idx] [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (word : List b.support)

private theorem word_ascent (hred : (weylCoxeterSystem b).IsReduced word)
    (n : ℕ) (hn : n < word.length) :
    b.IsPos (P.weylGroupToPerm (simpleWeylWord b (word.take n)) word[n]) := by
  apply isPos_of_length_mul_simple b _ word[n]
  have hs := (hred.take (n + 1)).eq
  have hp := (hred.take n).eq
  rw [weylCoxeterSystem_wordProd] at hs hp
  rw [word_next b word n hn, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hn)] at hs
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at hp
  exact hs.trans (congrArg (fun k => k + 1) hp.symm)
end Signs

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)

/-- Every next letter of a reduced word is an ascent from its preceding prefix. -/
theorem wordCell_ascent (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (n : ℕ) (hn : n < word.length) :
    G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (simpleWeylWord G.rootBase (word.take n)) word[n]) :=
  word_ascent G.rootBase word hred n hn

/-- The prefix-cell identification commutes with the inclusions into the flag variety. -/
theorem wordCellExtensionIso_flag (n : ℕ) (hn : n < word.length) :
    (wordCellExtensionIso G word n hn).hom ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1))) =
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n) *
          RootPairing.weylGroup.ofIdx G.rootSystem word[n]) := by
  unfold wordCellExtensionIso
  exact familyMap_cast (fun w : G.weylGroup => (schubertCell G w).toOver)
    (fun w : G.weylGroup => schubertCellInclusion G w)
    (word_next G.rootBase word n hn).symm

/-- The prefix-cell identification carries the word projection to the simple projection. -/
theorem wordCellExtensionIso_projection
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : ℕ) (hn : n < word.length)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
      (simpleWeylWord G.rootBase (word.take n)) word[n])) :
    (wordCellExtensionIso G word n hn).hom ≫ wordCellStep G word hred n =
      rankOneCellProjection G (simpleWeylWord G.rootBase (word.take n)) word[n] hi :=
  iso_cancel (wordCellExtensionIso G word n hn) (wordCellStep G word hred n) _
    (wordCellStep_eq G word hred n hn hi)

end
end SchubertGeometry
