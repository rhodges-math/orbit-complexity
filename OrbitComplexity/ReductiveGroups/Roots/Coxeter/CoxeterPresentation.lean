import OrbitComplexity.ReductiveGroups.Roots.Coxeter.SimpleGeneration
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The canonical Coxeter-presentation map to the Weyl group

The matrix entries are the orders of products of the base-simple
reflections. Their involutivity and distinctness prove the Coxeter-matrix
axioms. The universal presentation map sends each formal generator to its
reflection, agrees with every simple word, and is surjective
by the proved generation theorem.

Injectivity of this map is NOT proved here. Mathlib's `CoxeterSystem` on the
Weyl group requires an isomorphism with this presentation, so this
file does not define such a system or assume one as an input.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The Coxeter matrix of the simple-reflection product orders.
As in Mathlib, entry zero denotes infinite order. -/
def simpleCoxeterMatrix (b : P.Base) : CoxeterMatrix b.support where
  M i j := orderOf (RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j)
  isSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simpa only [mul_inv_rev, weylGroup_simple_inv] using
      orderOf_inv (RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j)
  diagonal i := by simp
  off_diagonal i j hij := by
    intro horder
    have hprod := orderOf_eq_one_iff.mp horder
    have heq : RootPairing.weylGroup.ofIdx P i = RootPairing.weylGroup.ofIdx P j := by
      simpa only [weylGroup_simple_inv] using mul_eq_one_iff_eq_inv.mp hprod
    exact hij (weylGroup_simple_injective b heq)

/-- The equality is

```lean
simpleCoxeterMatrix b i j =
      orderOf (RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j)
```
-/
@[simp] theorem simpleCoxeterMatrix_apply (b : P.Base) (i j : b.support) :
    simpleCoxeterMatrix b i j =
      orderOf (RootPairing.weylGroup.ofIdx P i * RootPairing.weylGroup.ofIdx P j) := rfl

/-- All defining relations hold for the simple reflections. -/
theorem simpleCoxeterMatrix_isLiftable (b : P.Base) :
    (simpleCoxeterMatrix b).IsLiftable
      (fun i : b.support => RootPairing.weylGroup.ofIdx P i) :=
  fun _ _ => pow_orderOf_eq_one _

/-- The canonical homomorphism from the Coxeter presentation. Its surjectivity
is proved below; injectivity is `weylCoxeterPresentationMap_injective`
(`Roots/PresentationWordPropertyCoxeter.lean`). -/
def weylCoxeterPresentationMap (b : P.Base) : (simpleCoxeterMatrix b).Group →* P.weylGroup :=
  (simpleCoxeterMatrix b).toCoxeterSystem.lift
    ⟨_, simpleCoxeterMatrix_isLiftable b⟩

/-- The equality is

```lean
weylCoxeterPresentationMap b ((simpleCoxeterMatrix b).simple i) =
      RootPairing.weylGroup.ofIdx P i
```
-/
@[simp] theorem weylCoxeterPresentationMap_simple (b : P.Base) (i : b.support) :
    weylCoxeterPresentationMap b ((simpleCoxeterMatrix b).simple i) =
      RootPairing.weylGroup.ofIdx P i :=
  (simpleCoxeterMatrix b).toCoxeterSystem.lift_apply_simple
    (simpleCoxeterMatrix_isLiftable b) i

/-- Formal word multiplication maps to the already-defined Weyl word,
with precisely the same order of factors. -/
@[simp] theorem weylCoxeterPresentationMap_wordProd (b : P.Base) (l : List b.support) :
    weylCoxeterPresentationMap b ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd l) =
      simpleWeylWord b l := by
  induction l with
  | nil => simp [simpleWeylWord]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul]
    simpa only [CoxeterMatrix.toCoxeterSystem_simple,
      weylCoxeterPresentationMap_simple, ih] using
        (show RootPairing.weylGroup.ofIdx P i * simpleWeylWord b l =
          simpleWeylWord b (i :: l) from rfl)

/-- Generation by base-simple reflections makes the presentation map onto. -/
theorem weylCoxeterPresentationMap_surjective (b : P.Base) :
    Function.Surjective (weylCoxeterPresentationMap b) := by
  intro w
  obtain ⟨l, hl⟩ := simpleWeylWord_surjective b w
  exact ⟨(simpleCoxeterMatrix b).toCoxeterSystem.wordProd l,
    (weylCoxeterPresentationMap_wordProd b l).trans hl⟩

/-- The braid relations by the Coxeter matrix hold for the
simple words. This does not assert completeness of braid moves between words. -/
theorem simpleWeylWord_braidWord_eq (b : P.Base) (i j : b.support) :
    simpleWeylWord b (CoxeterSystem.braidWord (simpleCoxeterMatrix b) i j) =
      simpleWeylWord b (CoxeterSystem.braidWord (simpleCoxeterMatrix b) j i) := by
  have h := congrArg (weylCoxeterPresentationMap b)
    ((simpleCoxeterMatrix b).toCoxeterSystem.wordProd_braidWord_eq i j)
  simpa only [weylCoxeterPresentationMap_wordProd] using h

end ReductiveGroups
