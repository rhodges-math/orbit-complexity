import OrbitComplexity.ReductiveGroups.Lie.Exponential.RadicalBracketNilpotence
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.ULift

/-!
# Associative Radical Nilpotence

The radical bracket has nilpotent images in finite associative representations. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

variable {K g A : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing g] [LieAlgebra K g] [Module.Finite K g]
  [Ring A] [Algebra K A] [FiniteDimensional K A]

attribute [local instance] LieRing.ofAssociativeRing

/-- Every element of the `[g, radical(g)]` has nilpotent image in a
finite-dimensional associative representation. -/
theorem AssociativeRadicalNilpotence.image_isNilpotent_of_mem_radicalBracket
    (f : g →ₗ⁅K⁆ A) {x : g}
    (hx : x ∈ (⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆ : LieIdeal K g)) :
    IsNilpotent (f x) := by
  let : LieRingModule A (ULift.{0} A) := LieRingModule.ofAssociativeModule
  let : LieModule K A (ULift.{0} A) := LieModule.ofAssociativeModule
  let : LieRingModule g (ULift.{0} A) := LieRingModule.compLieHom (ULift.{0} A) f
  let : LieModule K g (ULift.{0} A) := LieModule.compLieHom (ULift.{0} A) f
  have hn : IsNilpotent (toEnd K g (ULift.{0} A) x) :=
    radicalBracket_toEnd_isNilpotent (K := K) (g := g) (V := ULift.{0} A) hx
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  have hstep (a : A) :
      (toEnd K g (ULift.{0} A) x) (ULift.up a) = ULift.up ((f x) * a) := by
    rfl
  have hact (m : ℕ) : ∀ a : A,
      ((toEnd K g (ULift.{0} A) x) ^ m) (ULift.up a) = ULift.up ((f x) ^ m * a) := by
    induction m with
    | zero => intro a; simp
    | succ m ih =>
      intro a
      simp only [pow_succ, Module.End.mul_apply]
      rw [hstep, ih]
      simp only [mul_assoc]
  have hzero := congrArg (fun F : Module.End K (ULift.{0} A) => F (ULift.up (1 : A))) hn
  have hzero' := congrArg ULift.down hzero
  simpa [hact] using hzero'

end ReductiveGroups
