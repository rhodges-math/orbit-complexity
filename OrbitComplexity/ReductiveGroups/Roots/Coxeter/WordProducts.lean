import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordProperty
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Ordered products along reduced Weyl words -/

noncomputable section
namespace ReductiveGroups
open CoxeterSystem

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

private theorem braid_move_product_eq (b : P.Base) {H : Type*} [Monoid H]
    (f : b.support → H)
    (hbraid : ∀ i j, i ≠ j →
      ((braidWord (simpleCoxeterMatrix b) i j).map f).prod =
        ((braidWord (simpleCoxeterMatrix b) j i).map f).prod)
    {l k : List b.support} (h : WeylBraidMove b l k) :
    (l.map f).prod = (k.map f).prod := by
  obtain ⟨pre, post, i, j, hij, rfl, rfl⟩ := h
  simp only [List.map_append, List.prod_append]
  rw [hbraid i j hij]

private theorem braid_chain_product_eq (b : P.Base) {H : Type*} [Monoid H]
    (f : b.support → H)
    (hbraid : ∀ i j, i ≠ j →
      ((braidWord (simpleCoxeterMatrix b) i j).map f).prod =
        ((braidWord (simpleCoxeterMatrix b) j i).map f).prod)
    {l k : List b.support} (h : WeylBraidChain b l k) :
    (l.map f).prod = (k.map f).prod := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact ih.trans (braid_move_product_eq b f hbraid hm)

/-- Braid equations make ordered products independent of a reduced Weyl word. -/
theorem reduced_word_product_eq (b : P.Base) {H : Type*} [Monoid H]
    (f : b.support → H)
    (hbraid : ∀ i j, i ≠ j →
      ((braidWord (simpleCoxeterMatrix b) i j).map f).prod =
        ((braidWord (simpleCoxeterMatrix b) j i).map f).prod)
    {l k : List b.support} (hl : (weylCoxeterSystem b).IsReduced l)
    (hk : (weylCoxeterSystem b).IsReduced k)
    (heq : (weylCoxeterSystem b).wordProd l = (weylCoxeterSystem b).wordProd k) :
    (l.map f).prod = (k.map f).prod :=
  braid_chain_product_eq b f hbraid (weylCoxeterSystem_word_property b l k hl hk heq)

private theorem inverse_braid (b : P.Base) {H : Type*} [Group H]
    (f : b.support → H)
    (hbraid : ∀ i j, i ≠ j →
      ((braidWord (simpleCoxeterMatrix b) i j).map f).prod =
        ((braidWord (simpleCoxeterMatrix b) j i).map f).prod)
    (i j : b.support) (hij : i ≠ j) :
    ((braidWord (simpleCoxeterMatrix b) i j).map (fun s => (f s)⁻¹)).prod =
      ((braidWord (simpleCoxeterMatrix b) j i).map (fun s => (f s)⁻¹)).prod := by
  have hrev (l : List b.support) :
      (l.reverse.map (fun s => (f s)⁻¹)).prod = ((l.map f).prod)⁻¹ := by
    rw [List.prod_inv_reverse]
    simp only [List.map_reverse, List.map_map, Function.comp_def]
  have hh := congrArg Inv.inv (hbraid i j hij)
  rw [← hrev (braidWord (simpleCoxeterMatrix b) i j),
    ← hrev (braidWord (simpleCoxeterMatrix b) j i)] at hh
  simp only [braidWord, reverse_alternatingWord,
    (simpleCoxeterMatrix b).symmetric j i] at hh
  by_cases he : Even (simpleCoxeterMatrix b i j)
  · simpa only [braidWord, (simpleCoxeterMatrix b).symmetric j i, he, ite_true] using hh.symm
  · simpa only [braidWord, (simpleCoxeterMatrix b).symmetric j i, he, ite_false] using hh

/-- Inverses of braid generators have the same reduced-word independence. -/
theorem reduced_word_inv_product_eq (b : P.Base) {H : Type*} [Group H]
    (f : b.support → H)
    (hbraid : ∀ i j, i ≠ j →
      ((braidWord (simpleCoxeterMatrix b) i j).map f).prod =
        ((braidWord (simpleCoxeterMatrix b) j i).map f).prod)
    {l k : List b.support} (hl : (weylCoxeterSystem b).IsReduced l)
    (hk : (weylCoxeterSystem b).IsReduced k)
    (heq : (weylCoxeterSystem b).wordProd l = (weylCoxeterSystem b).wordProd k) :
    (l.map (fun s => (f s)⁻¹)).prod = (k.map (fun s => (f s)⁻¹)).prod :=
  reduced_word_product_eq b (fun s => (f s)⁻¹) (inverse_braid b f hbraid) hl hk heq

end ReductiveGroups
