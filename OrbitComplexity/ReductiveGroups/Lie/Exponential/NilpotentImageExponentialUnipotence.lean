import OrbitComplexity.ReductiveGroups.Lie.Exponential.RadicalExponentialUnipotence
import Mathlib.Algebra.Lie.Engel

/-!
# Nilpotent Image Exponential Unipotence

A finite-dimensional associative representation with all images nilpotent
has a uniform unipotence bound for every ordered word of exponentials. -/

noncomputable section
namespace ReductiveGroups
open LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K H A : Type*} [Field K] [CharZero K]
  [LieRing H] [LieAlgebra K H] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- The equality is

```lean
∃ N : ℕ, ∀ xs : List H,
      ((xs.map (fun x => associativeExponential (K := K) (f x))).prod - 1) ^ N = 0
```
-/
theorem NilpotentImageExponentialUnipotence.exists_unipotence_of_nilpotent_images
    (f : H →ₗ⁅K⁆ A) (hf : ∀ x : H, IsNilpotent (f x)) :
    ∃ N : ℕ, ∀ xs : List H,
      ((xs.map (fun x => associativeExponential (K := K) (f x))).prod - 1) ^ N = 0 := by
  let : LieRingModule A A := LieRingModule.ofAssociativeModule
  let : LieModule K A A := LieModule.ofAssociativeModule
  let : LieRingModule H A := LieRingModule.compLieHom A f
  let : LieModule K H A := LieModule.compLieHom A f
  have hto (x : H) : toEnd K H A x = (Algebra.lmul K A) (f x) := by
    ext a
    rfl
  have hnil (x : H) : IsNilpotent (toEnd K H A x) := by
    rw [hto]
    exact (hf x).map (Algebra.lmul K A)
  let : LieModule.IsNilpotent H A :=
    (LieModule.isNilpotent_iff_forall' (R := K) (L := H) (M := A)).mpr hnil
  obtain ⟨N, hN⟩ :=
    RadicalExponentialUnipotence.exists_unipotence_of_nilpotent_action (K := K) (H := H) (M := A)
  have hmapexp (x : H) :
      (Algebra.lmul K A) (associativeExponential (K := K) (f x)) =
        associativeExponential (K := K) ((Algebra.lmul K A) (f x)) := by
    let : Algebra ℚ K := (Rat.castHom K).toAlgebra
    let : Module ℚ A := Module.compHom A (algebraMap ℚ K)
    let : Module ℚ (Module.End K A) := Module.compHom (Module.End K A) (algebraMap ℚ K)
    exact IsNilpotent.map_exp (hf x) (Algebra.lmul K A)
  refine ⟨N, ?_⟩
  intro xs
  have hmap : (Algebra.lmul K A)
      (((xs.map (fun x => associativeExponential (K := K) (f x))).prod - 1) ^ N) = 0 := by
    simp only [map_pow, map_sub, map_one, map_list_prod, List.map_map]
    simpa only [Function.comp_def, hmapexp, hto] using hN xs
  have hinj : Function.Injective (Algebra.lmul K A) := by
    intro a b hab
    have h := congrArg (fun F : Module.End K A => F (1 : A)) hab
    simpa using h
  exact hinj (by simpa using hmap)

end ReductiveGroups
