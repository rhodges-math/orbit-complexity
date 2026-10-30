import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.TensorProduct.PointSeparation
import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWords
import Mathlib.Algebra.Category.CommAlgCat.Basic
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Derived Group Word Identity

Derived commutator words and separation on their universal tuple algebras. -/

noncomputable section
namespace ReductiveGroups

open WithConv
open scoped TensorProduct

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [IsReduced B]

/-- Coordinate algebra of all leaves of a balanced word. -/
def DerivedWordCoordinateAlg (K B : Type u) [Field K] [CommRing B] [HopfAlgebra K B] :
    ℕ → CommAlgCat K
  | 0 => CommAlgCat.of K B
  | n + 1 =>
      let A := DerivedWordCoordinateAlg K B n
      CommAlgCat.of K (A ⊗[K] A)

/-- The coordinate algebra of all leaves of a balanced derived word of depth `n`: the `2^n`-fold
tensor power of `B` over `K`, as a type. -/
abbrev DerivedWordCoordinates (K B : Type u) [Field K] [CommRing B] [HopfAlgebra K B]
    (n : ℕ) : Type u := DerivedWordCoordinateAlg K B n

/-- Evaluate the universal tuple algebra at one chosen rational point per leaf. -/
def derivedWordTupleEvaluation :
    (n : ℕ) → (DerivedWordIndex n → B →ₐ[K] K) →
      DerivedWordCoordinates K B n →ₐ[K] K
  | 0, x => x PUnit.unit
  | n + 1, x => Algebra.TensorProduct.productMap
      (derivedWordTupleEvaluation n (fun i => x (false, i)))
      (derivedWordTupleEvaluation n (fun i => x (true, i)))

/-- Evaluation at all tuples separates the finite tensor algebra.
This avoids a separate reducedness assumption on any tensor power. -/
theorem derivedWordTupleEvaluation_separates (n : ℕ)
    (a : DerivedWordCoordinates K B n)
    (ha : ∀ x : DerivedWordIndex n → B →ₐ[K] K,
      derivedWordTupleEvaluation n x a = 0) : a = 0 := by
  induction n with
  | zero =>
      have : Algebra.FiniteType K (DerivedWordCoordinates K B 0) := by
        change Algebra.FiniteType K B
        infer_instance
      have : IsReduced (DerivedWordCoordinates K B 0) := by
        change IsReduced B
        infer_instance
      change (a : B) = 0
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
      intro p
      simpa only [derivedWordTupleEvaluation, map_zero] using ha (fun _ => p)
  | succ n ih =>
      apply TauCeti.tensor_eq_zero_of_forall_productMap_eq_zero
        (fun l : DerivedWordIndex n → B →ₐ[K] K => derivedWordTupleEvaluation n l)
        (fun r : DerivedWordIndex n → B →ₐ[K] K => derivedWordTupleEvaluation n r)
      · intro z hz
        exact ih z hz
      · intro z hz
        exact ih z hz
      · intro l r
        exact ha (fun i => if i.1 then r i.2 else l i.2)

/-- The generic point at each leaf, valued in the tensor-coordinate algebra
representing the whole tuple. -/
def universalDerivedWordTuple :
    (n : ℕ) → DerivedWordIndex n →
      WithConv (B →ₐ[K] DerivedWordCoordinates K B n)
  | 0, _ => toConv (AlgHom.id K B)
  | n + 1, (false, i) =>
      TauCeti.AlgHom.mapValue (H := B)
        (Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := DerivedWordCoordinates K B n)
          (B := DerivedWordCoordinates K B n))
        (universalDerivedWordTuple n i)
  | n + 1, (true, i) =>
      TauCeti.AlgHom.mapValue (H := B)
        (Algebra.TensorProduct.includeRight (R := K)
          (A := DerivedWordCoordinates K B n)
          (B := DerivedWordCoordinates K B n))
        (universalDerivedWordTuple n i)

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] in
/-- The equality is

```lean
TauCeti.AlgHom.mapValue (derivedWordTupleEvaluation n x)
      (universalDerivedWordTuple n i) = toConv (x i)
```
-/
theorem universalDerivedWordTuple_eval (n : ℕ)
    (x : DerivedWordIndex n → B →ₐ[K] K) (i : DerivedWordIndex n) :
    TauCeti.AlgHom.mapValue (derivedWordTupleEvaluation n x)
      (universalDerivedWordTuple n i) = toConv (x i) := by
  induction n with
  | zero =>
      cases i
      apply WithConv.ofConv_injective
      ext a
      rfl
  | succ n ih =>
      rcases i with ⟨b, j⟩
      cases b
      · apply WithConv.ofConv_injective
        ext a
        have hh := congrArg (fun q : WithConv (B →ₐ[K] K) => q.ofConv a)
          (ih (fun k => x (false, k)) j)
        change (derivedWordTupleEvaluation n (fun k => x (false, k)))
          ((universalDerivedWordTuple n j).ofConv a) = x (false, j) a at hh
        change (Algebra.TensorProduct.productMap
          (derivedWordTupleEvaluation n (fun k => x (false, k)))
          (derivedWordTupleEvaluation n (fun k => x (true, k))))
          ((Algebra.TensorProduct.includeLeft (R := K) (S := K)
            (A := DerivedWordCoordinates K B n)
            (B := DerivedWordCoordinates K B n))
            ((universalDerivedWordTuple n j).ofConv a)) = x (false, j) a
        have hleft := Algebra.TensorProduct.productMap_left
          (derivedWordTupleEvaluation n (fun k => x (false, k)))
          (derivedWordTupleEvaluation n (fun k => x (true, k)))
        exact (congrArg (fun f : DerivedWordCoordinates K B n →ₐ[K] K =>
          f ((universalDerivedWordTuple n j).ofConv a)) hleft).trans hh
      · apply WithConv.ofConv_injective
        ext a
        have hh := congrArg (fun q : WithConv (B →ₐ[K] K) => q.ofConv a)
          (ih (fun k => x (true, k)) j)
        change (derivedWordTupleEvaluation n (fun k => x (true, k)))
          ((universalDerivedWordTuple n j).ofConv a) = x (true, j) a at hh
        change (Algebra.TensorProduct.productMap
          (derivedWordTupleEvaluation n (fun k => x (false, k)))
          (derivedWordTupleEvaluation n (fun k => x (true, k))))
          ((Algebra.TensorProduct.includeRight (R := K)
            (A := DerivedWordCoordinates K B n)
            (B := DerivedWordCoordinates K B n))
            ((universalDerivedWordTuple n j).ofConv a)) = x (true, j) a
        have hright := Algebra.TensorProduct.productMap_right
          (derivedWordTupleEvaluation n (fun k => x (false, k)))
          (derivedWordTupleEvaluation n (fun k => x (true, k)))
        exact (congrArg (fun f : DerivedWordCoordinates K B n →ₐ[K] K =>
          f ((universalDerivedWordTuple n j).ofConv a)) hright).trans hh

/-- Evaluation at all rational tuples separates generic points of the
original group valued in the universal tuple algebra. -/
theorem universalDerivedWord_point_separation (n : ℕ)
    (p q : WithConv (B →ₐ[K] DerivedWordCoordinates K B n))
    (h : ∀ x : DerivedWordIndex n → B →ₐ[K] K,
      TauCeti.AlgHom.mapValue (derivedWordTupleEvaluation n x) p =
        TauCeti.AlgHom.mapValue (derivedWordTupleEvaluation n x) q) : p = q := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  apply sub_eq_zero.mp
  apply derivedWordTupleEvaluation_separates n
  intro x
  have hh := congrArg (fun z : WithConv (B →ₐ[K] K) => z.ofConv b) (h x)
  simpa only [map_sub, TauCeti.AlgHom.mapValue_apply, toConv_ofConv,
    AlgHom.comp_apply, sub_eq_zero] using hh

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] in
/-- A balanced word evaluated at the universal tuple specializes to that
same word on every rational tuple. -/
theorem universalDerivedGroupWord_eval (n : ℕ)
    (x : DerivedWordIndex n → B →ₐ[K] K) :
    TauCeti.AlgHom.mapValue (derivedWordTupleEvaluation n x)
      (derivedGroupWord n (universalDerivedWordTuple (K := K) (B := B) n)) =
      derivedGroupWord n (fun i => toConv (x i)) := by
  rw [derivedGroupWord_map]
  congr 1
  funext i
  exact universalDerivedWordTuple_eval n x i

/-- A derived word that vanishes on every rational tuple already
vanishes at the universal tuple. -/
theorem UniversalDerivedGroupWord.eq_one_of_rational
    (n : ℕ)
    (h : ∀ x : DerivedWordIndex n → WithConv (B →ₐ[K] K),
      derivedGroupWord n x = 1) :
    derivedGroupWord n (universalDerivedWordTuple (K := K) (B := B) n) = 1 := by
  apply universalDerivedWord_point_separation n
  intro x
  rw [universalDerivedGroupWord_eval, map_one]
  exact h (fun i => toConv (x i))

/-- The universal tuple algebra maps to any commutative value algebra once
one point is chosen for every leaf. -/
def derivedWordTupleMap {A : Type*} [CommRing A] [Algebra K A] :
    (n : ℕ) → (DerivedWordIndex n → B →ₐ[K] A) →
      DerivedWordCoordinates K B n →ₐ[K] A
  | 0, x => x PUnit.unit
  | n + 1, x => Algebra.TensorProduct.productMap
      (derivedWordTupleMap n (fun i => x (false, i)))
      (derivedWordTupleMap n (fun i => x (true, i)))

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] in
/-- The equality is

```lean
TauCeti.AlgHom.mapValue (derivedWordTupleMap n x)
      (universalDerivedWordTuple n i) = toConv (x i)
```
-/
theorem universalDerivedWordTuple_map {A : Type*} [CommRing A] [Algebra K A]
    (n : ℕ) (x : DerivedWordIndex n → B →ₐ[K] A) (i : DerivedWordIndex n) :
    TauCeti.AlgHom.mapValue (derivedWordTupleMap n x)
      (universalDerivedWordTuple n i) = toConv (x i) := by
  induction n with
  | zero =>
      cases i
      apply WithConv.ofConv_injective
      ext a
      rfl
  | succ n ih =>
      rcases i with ⟨b, j⟩
      cases b
      · apply WithConv.ofConv_injective
        ext a
        have hh := congrArg (fun q : WithConv (B →ₐ[K] A) => q.ofConv a)
          (ih (fun k => x (false, k)) j)
        change (derivedWordTupleMap n (fun k => x (false, k)))
          ((universalDerivedWordTuple n j).ofConv a) = x (false, j) a at hh
        change (Algebra.TensorProduct.productMap
          (derivedWordTupleMap n (fun k => x (false, k)))
          (derivedWordTupleMap n (fun k => x (true, k))))
          ((Algebra.TensorProduct.includeLeft (R := K) (S := K)
            (A := DerivedWordCoordinates K B n)
            (B := DerivedWordCoordinates K B n))
            ((universalDerivedWordTuple n j).ofConv a)) = x (false, j) a
        have hleft := Algebra.TensorProduct.productMap_left
          (derivedWordTupleMap n (fun k => x (false, k)))
          (derivedWordTupleMap n (fun k => x (true, k)))
        exact (congrArg (fun f : DerivedWordCoordinates K B n →ₐ[K] A =>
          f ((universalDerivedWordTuple n j).ofConv a)) hleft).trans hh
      · apply WithConv.ofConv_injective
        ext a
        have hh := congrArg (fun q : WithConv (B →ₐ[K] A) => q.ofConv a)
          (ih (fun k => x (true, k)) j)
        change (derivedWordTupleMap n (fun k => x (true, k)))
          ((universalDerivedWordTuple n j).ofConv a) = x (true, j) a at hh
        change (Algebra.TensorProduct.productMap
          (derivedWordTupleMap n (fun k => x (false, k)))
          (derivedWordTupleMap n (fun k => x (true, k))))
          ((Algebra.TensorProduct.includeRight (R := K)
            (A := DerivedWordCoordinates K B n)
            (B := DerivedWordCoordinates K B n))
            ((universalDerivedWordTuple n j).ofConv a)) = x (true, j) a
        have hright := Algebra.TensorProduct.productMap_right
          (derivedWordTupleMap n (fun k => x (false, k)))
          (derivedWordTupleMap n (fun k => x (true, k)))
        exact (congrArg (fun f : DerivedWordCoordinates K B n →ₐ[K] A =>
          f ((universalDerivedWordTuple n j).ofConv a)) hright).trans hh

/-- Vanishing of a derived group word on every ground-field tuple
implies the same word identity for points valued in every commutative
`K`-algebra. -/
theorem derivedGroupWord_eq_one_of_rational
    (n : ℕ)
    (h : ∀ x : DerivedWordIndex n → WithConv (B →ₐ[K] K),
      derivedGroupWord n x = 1)
    {A : Type*} [CommRing A] [Algebra K A]
    (x : DerivedWordIndex n → WithConv (B →ₐ[K] A)) :
    derivedGroupWord n x = 1 := by
  let φ := derivedWordTupleMap n (fun i => (x i).ofConv)
  have hgeneric := UniversalDerivedGroupWord.eq_one_of_rational n h
  have hmap := congrArg (TauCeti.AlgHom.mapValue (H := B) φ) hgeneric
  rw [derivedGroupWord_map, map_one] at hmap
  have htuple : ∀ i, TauCeti.AlgHom.mapValue φ (universalDerivedWordTuple n i) = x i := by
    intro i
    simpa only [toConv_ofConv] using
      universalDerivedWordTuple_map n (fun j => (x j).ofConv) i
  simpa only [htuple] using hmap
end ReductiveGroups
