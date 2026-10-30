import OrbitComplexity.Paper.BruhatExamples.Permutations
import OrbitComplexity.BruhatIntervals.Permutations.Intervals
import OrbitComplexity.BruhatIntervals.Graph.Support
import OrbitComplexity.BruhatIntervals.Graph.Labels

/-!
# Boolean intervals with different toric properties

Both `[1324,4231]` and `[12345,51234]` have the order type of subsets of a four-element set.
The first has algebraic dimension at most three and length four; the second has both support
cardinality and length four.
-/

namespace SchubertOrbits.BruhatExamples

open BruhatIntervals

private def fourAtoms (i : Fin 4) : Equiv.Perm (Fin 4) :=
  TypeA.wordPermutation 3
    (if i = 0 then [1, 2] else if i = 1 then [2, 1] else if i = 2 then [0, 1] else [1, 0])

private def encodeFour (w : Equiv.Perm (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => fourAtoms i ∈ TypeA.subwordProducts 3 w)

private def encodeFive (w : Equiv.Perm (Fin 5)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => TypeA.simpleReflection 4 i ∈ TypeA.subwordProducts 4 w)

set_option maxRecDepth 4096 in
private theorem first_boolean :
    let : PartialOrder (Equiv.Perm (Fin 4)) := (TypeA.coxeterSystem 3).bruhatPartialOrder
    Nonempty ((Finset (Fin 4)) ≃o
      bruhatInterval (TypeA.coxeterSystem 3) lower1324 upper4231) := by
  let : PartialOrder (Equiv.Perm (Fin 4)) := (TypeA.coxeterSystem 3).bruhatPartialOrder
  have htable : ∀ x y : Equiv.Perm (Fin 4),
      x ∈ TypeA.intervalElements 3 lower1324 upper4231 →
      y ∈ TypeA.intervalElements 3 lower1324 upper4231 →
      (x ∈ TypeA.subwordProducts 3 y ↔ encodeFour x ⊆ encodeFour y) := by decide
  have hattain : ∀ a : Finset (Fin 4), ∃ w : Equiv.Perm (Fin 4),
      w ∈ TypeA.intervalElements 3 lower1324 upper4231 ∧ encodeFour w = a := by decide
  let encode : bruhatInterval (TypeA.coxeterSystem 3) lower1324 upper4231 →
      Finset (Fin 4) := fun w => encodeFour w.val
  have horder (x y : bruhatInterval (TypeA.coxeterSystem 3) lower1324 upper4231) :
      x ≤ y ↔ encode x ⊆ encode y := by
    change (TypeA.coxeterSystem 3).BruhatLE x.val y.val ↔ _
    rw [← TypeA.mem_subwordProducts]
    exact htable x.val y.val ((TypeA.mem_intervalElements 3 _ _ _).mpr x.property)
      ((TypeA.mem_intervalElements 3 _ _ _).mpr y.property)
  have hinjective : Function.Injective encode := by
    intro x y hxy
    apply le_antisymm
    · exact (horder x y).mpr (le_of_eq hxy)
    · exact (horder y x).mpr (le_of_eq hxy.symm)
  have hsurjective : Function.Surjective encode := by
    intro a
    obtain ⟨w, hmem, hencode⟩ := hattain a
    exact ⟨⟨w, (TypeA.mem_intervalElements 3 _ _ _).mp hmem⟩, hencode⟩
  let iso : bruhatInterval (TypeA.coxeterSystem 3) lower1324 upper4231 ≃o
      Finset (Fin 4) :=
    { toEquiv := Equiv.ofBijective encode ⟨hinjective, hsurjective⟩
      map_rel_iff' := fun {x y} => (horder x y).symm }
  exact ⟨iso.symm⟩

set_option maxRecDepth 4096 in
private theorem second_boolean :
    let : PartialOrder (Equiv.Perm (Fin 5)) := (TypeA.coxeterSystem 4).bruhatPartialOrder
    Nonempty ((Finset (Fin 4)) ≃o
      bruhatInterval (TypeA.coxeterSystem 4) 1 upper51234) := by
  let : PartialOrder (Equiv.Perm (Fin 5)) := (TypeA.coxeterSystem 4).bruhatPartialOrder
  have htable : ∀ x y : Equiv.Perm (Fin 5),
      x ∈ TypeA.intervalElements 4 1 upper51234 →
      y ∈ TypeA.intervalElements 4 1 upper51234 →
      (x ∈ TypeA.subwordProducts 4 y ↔ encodeFive x ⊆ encodeFive y) := by decide
  have hattain : ∀ a : Finset (Fin 4), ∃ w : Equiv.Perm (Fin 5),
      w ∈ TypeA.intervalElements 4 1 upper51234 ∧ encodeFive w = a := by decide
  let encode : bruhatInterval (TypeA.coxeterSystem 4) 1 upper51234 →
      Finset (Fin 4) := fun w => encodeFive w.val
  have horder (x y : bruhatInterval (TypeA.coxeterSystem 4) 1 upper51234) :
      x ≤ y ↔ encode x ⊆ encode y := by
    change (TypeA.coxeterSystem 4).BruhatLE x.val y.val ↔ _
    rw [← TypeA.mem_subwordProducts]
    exact htable x.val y.val ((TypeA.mem_intervalElements 4 _ _ _).mpr x.property)
      ((TypeA.mem_intervalElements 4 _ _ _).mpr y.property)
  have hinjective : Function.Injective encode := by
    intro x y hxy
    apply le_antisymm
    · exact (horder x y).mpr (le_of_eq hxy)
    · exact (horder y x).mpr (le_of_eq hxy.symm)
  have hsurjective : Function.Surjective encode := by
    intro a
    obtain ⟨w, hmem, hencode⟩ := hattain a
    exact ⟨⟨w, (TypeA.mem_intervalElements 4 _ _ _).mp hmem⟩, hencode⟩
  let iso : bruhatInterval (TypeA.coxeterSystem 4) 1 upper51234 ≃o
      Finset (Fin 4) :=
    { toEquiv := Equiv.ofBijective encode ⟨hinjective, hsurjective⟩
      map_rel_iff' := fun {x y} => (horder x y).symm }
  exact ⟨iso.symm⟩

private theorem first_not_toric :
    ¬ IsToricInterval (TypeA.realization 3) lower1324 upper4231 := by
  have hsupport : supportCard (TypeA.coxeterSystem 3) upper4231 = 3 := by
    have hset : support (TypeA.coxeterSystem 3) upper4231 =
        (TypeA.coxeterSystem 3).simple ''
          (↑(TypeA.reducedWord 3 upper4231).toFinset : Set (Fin 3)) := by
      rw [support_eq_letters (TypeA.coxeterSystem 3)
        (TypeA.reducedWord_spec 3 upper4231).1 (TypeA.reducedWord_spec 3 upper4231).2]
      ext t
      simp
    rw [supportCard, hset, Set.ncard_image_of_injective _
      (simple_injective (TypeA.coxeterSystem 3)), Set.ncard_coe_finset]
    decide
  have hbound : algebraicDim (TypeA.realization 3) lower1324 upper4231 ≤ 3 := by
    have hspan := labelSpan_mono (TypeA.realization 3)
      ((TypeA.coxeterSystem 3).one_bruhatLE lower1324)
      (Relation.ReflTransGen.refl : (TypeA.coxeterSystem 3).BruhatLE upper4231 upper4231)
    have hdim := Submodule.finrank_mono hspan
    rwa [← algebraicDim, ← algebraicDim, algebraicDim_one, hsupport] at hdim
  have hlow : (TypeA.coxeterSystem 3).length lower1324 = 1 := by
    rw [TypeA.length_eq_inversions]
    unfold TypeA.inversionPairs
    rw [show (⇑lower1324 : Fin 4 → Fin 4) =
      (fun i => if i = 1 then 2 else if i = 2 then 1 else i) from funext lower1324_apply]
    decide
  have hhigh : (TypeA.coxeterSystem 3).length upper4231 = 5 := by
    rw [TypeA.length_eq_inversions]
    unfold TypeA.inversionPairs
    rw [show (⇑upper4231 : Fin 4 → Fin 4) =
      (fun i => if i = 0 then 3 else if i = 3 then 0 else i) from funext upper4231_apply]
    decide
  intro htoric
  change algebraicDim (TypeA.realization 3) lower1324 upper4231 =
    (TypeA.coxeterSystem 3).length upper4231 -
      (TypeA.coxeterSystem 3).length lower1324 at htoric
  rw [hlow, hhigh] at htoric
  omega

private theorem second_toric : IsToricInterval (TypeA.realization 4) 1 upper51234 := by
  have hsupport : supportCard (TypeA.coxeterSystem 4) upper51234 = 4 := by
    have hset : support (TypeA.coxeterSystem 4) upper51234 =
        (TypeA.coxeterSystem 4).simple ''
          (↑(TypeA.reducedWord 4 upper51234).toFinset : Set (Fin 4)) := by
      rw [support_eq_letters (TypeA.coxeterSystem 4)
        (TypeA.reducedWord_spec 4 upper51234).1 (TypeA.reducedWord_spec 4 upper51234).2]
      ext t
      simp
    rw [supportCard, hset, Set.ncard_image_of_injective _
      (simple_injective (TypeA.coxeterSystem 4)), Set.ncard_coe_finset]
    decide
  have hlength : (TypeA.coxeterSystem 4).length upper51234 = 4 := by
    rw [TypeA.length_eq_inversions]
    unfold TypeA.inversionPairs
    rw [show (⇑upper51234 : Fin 5 → Fin 5) =
      (fun i => if i = 0 then 4 else i - 1) from funext upper51234_apply]
    decide
  change algebraicDim (TypeA.realization 4) 1 upper51234 =
    (TypeA.coxeterSystem 4).length upper51234 - (TypeA.coxeterSystem 4).length 1
  rw [algebraicDim_one, hsupport, hlength, (TypeA.coxeterSystem 4).length_one]

/-- Two Bruhat intervals have the Boolean rank-four order type, while only the second is toric. -/
theorem boolean_toric_intervals :
    let : PartialOrder (Equiv.Perm (Fin 4)) := (TypeA.coxeterSystem 3).bruhatPartialOrder
    let : PartialOrder (Equiv.Perm (Fin 5)) := (TypeA.coxeterSystem 4).bruhatPartialOrder
    Nonempty ((Finset (Fin 4)) ≃o
      bruhatInterval (TypeA.coxeterSystem 3) lower1324 upper4231) ∧
      ¬ IsToricInterval (TypeA.realization 3) lower1324 upper4231 ∧
      Nonempty ((Finset (Fin 4)) ≃o
        bruhatInterval (TypeA.coxeterSystem 4) 1 upper51234) ∧
      IsToricInterval (TypeA.realization 4) 1 upper51234 := by
  exact ⟨first_boolean, first_not_toric, second_boolean, second_toric⟩

end SchubertOrbits.BruhatExamples
