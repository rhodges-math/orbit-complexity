import OrbitComplexity.ReductiveGroups.Lie.Roots.AssociativeRadicalWordBound
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentExponentialConjugation

/-!
# Radical Exponential Unipotence

Uniform unipotence of arbitrary products of radical-bracket exponentials. -/

noncomputable section
namespace ReductiveGroups
open LieModule

variable {K H M : Type*} [Field K] [CharZero K]
  [LieRing H] [LieAlgebra K H]
  [AddCommGroup M] [Module K M] [LieRingModule H M] [LieModule K H M]

/-- Endomorphisms that lower every step of the module lower-central filtration. -/
private def lowerCentralLowering : Submodule K (Module.End K M) where
  carrier := {T | ∀ k (m : M), m ∈ lowerCentralSeries K H M k →
    T m ∈ lowerCentralSeries K H M (k + 1)}
  zero_mem' := by intro k m hm; simp
  add_mem' := by
    intro T U hT hU k m hm
    exact (lowerCentralSeries K H M (k + 1)).add_mem (hT k m hm) (hU k m hm)
  smul_mem' := by
    intro c T hT k m hm
    exact (lowerCentralSeries K H M (k + 1)).smul_mem c (hT k m hm)

omit [CharZero K] [LieModule K H M] in
private theorem lowerCentralLowering_mul
    {T U : Module.End K M} (hT : T ∈ lowerCentralLowering (K := K) (H := H) (M := M))
    (hU : U ∈ lowerCentralLowering (K := K) (H := H) (M := M)) :
    T * U ∈ lowerCentralLowering (K := K) (H := H) (M := M) := by
  intro k m hm
  change T (U m) ∈ lowerCentralSeries K H M (k + 1)
  exact (antitone_lowerCentralSeries K H M (Nat.le_succ (k + 1)))
    (hT (k + 1) (U m) (hU k m hm))

omit [CharZero K] in
private theorem toEnd_mem_lowerCentralLowering (x : H) :
    toEnd K H M x ∈ lowerCentralLowering (K := K) (H := H) (M := M) := by
  intro k m hm
  rw [lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hm

omit [CharZero K] [LieModule K H M] in
private theorem lowerCentralLowering_pow {T : Module.End K M}
    (hT : T ∈ lowerCentralLowering (K := K) (H := H) (M := M))
    (n : ℕ) : T ^ (n + 1) ∈ lowerCentralLowering (K := K) (H := H) (M := M) := by
  induction n with
  | zero => simpa using hT
  | succ n ih =>
      rw [pow_succ]
      exact lowerCentralLowering_mul ih hT

omit [LieModule K H M] in
private theorem lowerCentralLowering_exp_sub_one
    {T : Module.End K M} (hT : T ∈ lowerCentralLowering (K := K) (H := H) (M := M))
    (hnil : IsNilpotent T) :
    associativeExponential (K := K) T - 1 ∈
      lowerCentralLowering (K := K) (H := H) (M := M) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Module.End K M) :=
    Module.compHom (Module.End K M) (algebraMap ℚ K)
  obtain ⟨n, hn⟩ := hnil
  have hn' : T ^ (n + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ n) hn
  change IsNilpotent.exp T - 1 ∈ lowerCentralLowering (K := K) (H := H) (M := M)
  rw [IsNilpotent.exp_eq_sum hn', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  change (algebraMap ℚ K (((i + 1).factorial : ℚ)⁻¹) • T ^ (i + 1)) ∈
    lowerCentralLowering (K := K) (H := H) (M := M)
  exact (lowerCentralLowering (K := K) (H := H) (M := M)).smul_mem _
    (lowerCentralLowering_pow hT i)

omit [CharZero K] [LieModule K H M] in
private theorem lowerCentralLowering_pow_eq_zero
    (N : ℕ) (hN : lowerCentralSeries K H M N = ⊥)
    {T : Module.End K M}
    (hT : T ∈ lowerCentralLowering (K := K) (H := H) (M := M)) :
    T ^ N = 0 := by
  have hpow (k : ℕ) (m : M) : (T ^ k) m ∈ lowerCentralSeries K H M k := by
    induction k with
    | zero => simp only [pow_zero, Module.End.one_apply, lowerCentralSeries_zero,
        LieSubmodule.mem_top]
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hT k ((T ^ k) m) ih
  ext m
  have hm := hpow N m
  rw [hN] at hm
  exact (LieSubmodule.mem_bot _).mp hm

/-- Uniform unipotence of all finite products of exponentials of a nilpotent
Lie-module action. The exponent comes from its lower central series. -/
theorem RadicalExponentialUnipotence.exists_unipotence_of_nilpotent_action
    [LieModule.IsNilpotent H M] :
    ∃ N : ℕ, ∀ xs : List H,
      ((xs.map (fun x => associativeExponential (K := K) (toEnd K H M x))).prod - 1) ^ N = 0 := by
  obtain ⟨N, hN⟩ := LieModule.IsNilpotent.nilpotent K H M
  refine ⟨N, ?_⟩
  have hlist (xs : List H) :
      (xs.map (fun x => associativeExponential (K := K) (toEnd K H M x))).prod - 1 ∈
        lowerCentralLowering (K := K) (H := H) (M := M) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        let E := associativeExponential (K := K) (toEnd K H M x)
        let P := (xs.map (fun y => associativeExponential (K := K) (toEnd K H M y))).prod
        have hx : E - 1 ∈ lowerCentralLowering (K := K) (H := H) (M := M) :=
          lowerCentralLowering_exp_sub_one (toEnd_mem_lowerCentralLowering x)
            (LieModule.isNilpotent_toEnd_of_isNilpotent K H M x)
        have hident : E * P - 1 = (E - 1) + (P - 1) + (E - 1) * (P - 1) := by
          noncomm_ring
        simpa only [List.map_cons, List.prod_cons, E, P, hident] using
          (lowerCentralLowering (K := K) (H := H) (M := M)).add_mem
            ((lowerCentralLowering (K := K) (H := H) (M := M)).add_mem hx ih)
            (lowerCentralLowering_mul hx ih)
  intro xs
  exact lowerCentralLowering_pow_eq_zero N hN (hlist xs)

variable {g A : Type*} [LieRing g] [LieAlgebra K g] [Module.Finite K g]
  [IsAlgClosed K] [Ring A] [Algebra K A] [FiniteDimensional K A]

attribute [local instance 100] LieRing.ofAssociativeRing

omit [IsAlgClosed K] [FiniteDimensional K A] in
private theorem lmul_associativeExponential (x : A) (hx : IsNilpotent x) :
    (Algebra.lmul K A) (associativeExponential (K := K) x) =
      associativeExponential (K := K) ((Algebra.lmul K A) x) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  let : Module ℚ (Module.End K A) :=
    Module.compHom (Module.End K A) (algebraMap ℚ K)
  exact IsNilpotent.map_exp hx (Algebra.lmul K A)

/-- A single exponent works for every finite product of exponentials of
arbitrary elements of `[g, radical(g)]` in a finite associative representation.
No commutativity among the factors is required. -/
theorem RadicalExponentialUnipotence.exists_exponential_product_unipotence
    (f : g →ₗ⁅K⁆ A) :
    ∃ N : ℕ, ∀ xs : List
      (↥(⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆ : LieIdeal K g)),
      ((xs.map (fun (x : ↥(⁅(⊤ : LieIdeal K g),
        LieAlgebra.radical K g⁆ : LieIdeal K g)) =>
          associativeExponential (K := K) (f (x : g)))).prod - 1) ^ N = 0 := by
  let H : LieIdeal K g := ⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆
  let : LieRingModule A A := LieRingModule.ofAssociativeModule
  let : LieModule K A A := LieModule.ofAssociativeModule
  let : LieRingModule g A := LieRingModule.compLieHom A f
  let : LieModule K g A := LieModule.compLieHom A f
  let : LieModule.IsNilpotent H A :=
    radicalBracket_action_isNilpotent (K := K) (g := g) (V := A)
  obtain ⟨N, hN⟩ :=
    RadicalExponentialUnipotence.exists_unipotence_of_nilpotent_action (K := K) (H := H) (M := A)
  refine ⟨N, ?_⟩
  intro xs
  have hto (x : H) : toEnd K H A x = (Algebra.lmul K A) (f (x : g)) := by
    ext a
    rfl
  have hmapexp (x : H) :
      (Algebra.lmul K A) (associativeExponential (K := K) (f (x : g))) =
        associativeExponential (K := K) ((Algebra.lmul K A) (f (x : g))) :=
    lmul_associativeExponential (f (x : g))
      (AssociativeRadicalNilpotence.image_isNilpotent_of_mem_radicalBracket f x.property)
  have hmap : (Algebra.lmul K A)
      (((xs.map (fun (x : H) => associativeExponential (K := K) (f (x : g)))).prod - 1) ^ N) =
      0 := by
    simp only [map_pow, map_sub, map_one, map_list_prod, List.map_map]
    simpa only [Function.comp_def, hmapexp, hto] using hN xs
  have hinj : Function.Injective (Algebra.lmul K A) := by
    intro a b hab
    have h := congrArg (fun F : Module.End K A => F (1 : A)) hab
    simpa using h
  exact hinj (by simpa using hmap)

end ReductiveGroups
