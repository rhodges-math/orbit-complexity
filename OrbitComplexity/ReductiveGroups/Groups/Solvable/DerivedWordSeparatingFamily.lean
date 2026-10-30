import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWordIdentity

/-!
# Derived Word Separating Family

A balanced group-word identity on any algebraically separating family of
rational points extends to points in every commutative value algebra. No
topological density or reducedness premise is substituted for separation. -/

noncomputable section
namespace ReductiveGroups
open WithConv

universe u v
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  {ι : Type v} (p : ι → B →ₐ[K] K)

/-- The equality is

```lean
a = 0
```
-/
theorem DerivedWordTupleEvaluation.separates_family
    (hp : ∀ a : B, (∀ i, p i a = 0) → a = 0)
    (n : ℕ) (a : DerivedWordCoordinates K B n)
    (ha : ∀ x : DerivedWordIndex n → ι,
      derivedWordTupleEvaluation n (fun i => p (x i)) a = 0) : a = 0 := by
  induction n with
  | zero => exact hp a (fun i => ha (fun _ => i))
  | succ n ih =>
      apply TauCeti.tensor_eq_zero_of_forall_productMap_eq_zero
        (fun l : DerivedWordIndex n → ι => derivedWordTupleEvaluation n (fun i => p (l i)))
        (fun r : DerivedWordIndex n → ι => derivedWordTupleEvaluation n (fun i => p (r i)))
      · intro z hz
        exact ih z hz
      · intro z hz
        exact ih z hz
      · intro l r
        exact ha (fun i => if i.1 then r i.2 else l i.2)

/-- The equality is

```lean
derivedGroupWord n (universalDerivedWordTuple (K := K) (B := B) n) = 1
```
-/
theorem UniversalDerivedGroupWord.eq_one_of_separating_family
    (hp : ∀ a : B, (∀ i, p i a = 0) → a = 0)
    (n : ℕ)
    (h : ∀ x : DerivedWordIndex n → ι,
      derivedGroupWord n (fun i => toConv (p (x i))) = 1) :
    derivedGroupWord n (universalDerivedWordTuple (K := K) (B := B) n) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  apply sub_eq_zero.mp
  apply DerivedWordTupleEvaluation.separates_family p hp n
  intro x
  have hh := universalDerivedGroupWord_eval n (fun i => p (x i))
  rw [h x] at hh
  have hunit := (TauCeti.AlgHom.mapValue (H := B)
    (derivedWordTupleEvaluation n (fun i => p (x i)))).map_one
  have heq := congrArg (fun z : WithConv (B →ₐ[K] K) => z.ofConv b)
    (hh.trans hunit.symm)
  simpa only [map_sub, TauCeti.AlgHom.mapValue_apply, toConv_ofConv,
    AlgHom.comp_apply, sub_eq_zero] using heq

/-- The equality is

```lean
derivedGroupWord n x = 1
```
-/
theorem DerivedGroupWord.eq_one_of_separating_family
    (hp : ∀ a : B, (∀ i, p i a = 0) → a = 0)
    (n : ℕ)
    (h : ∀ x : DerivedWordIndex n → ι,
      derivedGroupWord n (fun i => toConv (p (x i))) = 1)
    {A : Type*} [CommRing A] [Algebra K A]
    (x : DerivedWordIndex n → WithConv (B →ₐ[K] A)) :
    derivedGroupWord n x = 1 := by
  let φ := derivedWordTupleMap n (fun i => (x i).ofConv)
  have hgeneric := UniversalDerivedGroupWord.eq_one_of_separating_family p hp n h
  have hmap := congrArg (TauCeti.AlgHom.mapValue (H := B) φ) hgeneric
  rw [derivedGroupWord_map, map_one] at hmap
  have htuple : ∀ i, TauCeti.AlgHom.mapValue φ (universalDerivedWordTuple n i) = x i := by
    intro i
    simpa only [toConv_ofConv] using
      universalDerivedWordTuple_map n (fun j => (x j).ofConv) i
  simpa only [htuple] using hmap

end ReductiveGroups
