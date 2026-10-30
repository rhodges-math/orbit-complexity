import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Derivation Local Nilpotence

The elements killed by some iterate of a derivation form a subalgebra.
This supplies local nilpotence from algebra generators without a triangular
coordinate choice. -/

noncomputable section
namespace ReductiveGroups

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

private theorem derivation_pow_apply_next (D : Derivation K A A) (m : ℕ) (a : A) :
    (D.toLinearMap ^ m) (D a) = (D.toLinearMap ^ (m + 1)) a := by
  rw [pow_succ]
  rfl

/-- A sufficient product bound; the slightly larger exponent avoids
subtracting one and includes zero exponents. -/
theorem derivation_pow_mul_eq_zero (D : Derivation K A A) {m n : ℕ} {a b : A}
    (ha : (D.toLinearMap ^ m) a = 0) (hb : (D.toLinearMap ^ n) b = 0) :
    (D.toLinearMap ^ (m + n)) (a * b) = 0 := by
  induction m generalizing n a b with
  | zero =>
    have ha' : a = 0 := ha
    simp [ha']
  | succ m ihm =>
    induction n generalizing a b with
    | zero =>
      have hb' : b = 0 := hb
      simp [hb']
    | succ n ihn =>
      have hDa : (D.toLinearMap ^ m) (D a) = 0 := by
        rw [derivation_pow_apply_next]
        exact ha
      have hDb : (D.toLinearMap ^ n) (D b) = 0 := by
        rw [derivation_pow_apply_next]
        exact hb
      have hab : (D.toLinearMap ^ (m + 1 + n)) (a * D b) = 0 := ihn ha hDb
      have hba : (D.toLinearMap ^ (m + (n + 1))) (D a * b) = 0 := ihm hDa hb
      rw [show m + 1 + (n + 1) = (m + 1 + n) + 1 by omega,
        ← derivation_pow_apply_next, D.leibniz]
      change (D.toLinearMap ^ (m + 1 + n)) (a * D b + b * D a) = 0
      rw [map_add, hab, mul_comm b (D a),
        show m + 1 + n = m + (n + 1) by omega, hba, add_zero]

/-- The elements locally killed by a derivation form a subalgebra. -/
def derivationNilpotentSubalgebra (D : Derivation K A A) : Subalgebra K A where
  carrier := {a | ∃ m : ℕ, (D.toLinearMap ^ m) a = 0}
  algebraMap_mem' := by
    intro r
    exact ⟨1, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have ha : (D.toLinearMap ^ (m + n)) a = 0 := by
      rw [Nat.add_comm, pow_add, Module.End.mul_apply, hm, map_zero]
    have hb : (D.toLinearMap ^ (m + n)) b = 0 := by
      rw [pow_add, Module.End.mul_apply, hn, map_zero]
    rw [map_add, ha, hb, add_zero]
  mul_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, derivation_pow_mul_eq_zero D hm hn⟩

/-- Local nilpotence on any algebra-generating set suffices for local
nilpotence on every algebra element. -/
theorem DerivationLocalNilpotence.locally_nilpotent_of_generators (D : Derivation K A A)
    (S : Set A) (hS : Algebra.adjoin K S = ⊤)
    (hD : ∀ a ∈ S, ∃ m : ℕ, (D.toLinearMap ^ m) a = 0) :
    ∀ a : A, ∃ m : ℕ, (D.toLinearMap ^ m) a = 0 := by
  have hle : Algebra.adjoin K S ≤ derivationNilpotentSubalgebra D :=
    Algebra.adjoin_le hD
  rw [hS] at hle
  exact fun a => hle (show a ∈ (⊤ : Subalgebra K A) from trivial)

private theorem end_pow_apply_eq_zero_of_le
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : Module.End K V) {m n : ℕ} {v : V}
    (h : (f ^ m) v = 0) (hmn : m ≤ n) : (f ^ n) v = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_comm, pow_add, Module.End.mul_apply, h, map_zero]

/-- Pointwise local nilpotence becomes a uniform nilpotence exponent in
finite dimension. -/
theorem end_isNilpotent_of_locally_nilpotent
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : ∀ v : V, ∃ m : ℕ, (f ^ m) v = 0) :
    IsNilpotent f := by
  classical
  let b := Module.finBasis K V
  choose n hn using fun i => hf (b i)
  refine ⟨∑ i, n i, ?_⟩
  apply b.ext
  intro i
  change (f ^ (∑ i, n i)) (b i) = 0
  exact end_pow_apply_eq_zero_of_le f (hn i)
    (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i))

/-- Restricting a locally nilpotent operator to an invariant finite space
gives a nilpotent endomorphism of that space. -/
theorem DerivationLocalNilpotence.isNilpotent_of_locally_nilpotent
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (W : Submodule K V) [FiniteDimensional K W]
    (hW : W ∈ f.invtSubmodule)
    (hf : ∀ v ∈ W, ∃ m : ℕ, (f ^ m) v = 0) :
    IsNilpotent (f.restrict hW) := by
  have hW' : ∀ v ∈ W, f v ∈ W := fun _ hv => hW hv
  change IsNilpotent (f.restrict hW')
  apply end_isNilpotent_of_locally_nilpotent
  intro v
  obtain ⟨m, hm⟩ := hf v v.property
  refine ⟨m, ?_⟩
  rw [Module.End.pow_restrict]
  apply Subtype.ext
  exact hm

end ReductiveGroups
