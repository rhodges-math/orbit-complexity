import Mathlib.Algebra.Lie.Weights.Chain
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.ULift

/-!
# Associative Root Nilpotence

Nonzero Lie roots act by nilpotent elements in finite associative representations. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

variable {K L A : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L]
  [Ring A] [Algebra K A] [FiniteDimensional K A]

attribute [local instance] LieRing.ofAssociativeRing

/-- The image of a nonzero Lie-root vector in any finite-dimensional
associative representation is nilpotent as an associative element. -/
theorem AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace
    (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
    (f : L →ₗ⁅K⁆ A) {x : L} {χ : H → K}
    (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    IsNilpotent (f x) := by
  let : LieRingModule A (ULift.{0} A) := LieRingModule.ofAssociativeModule
  let : LieModule K A (ULift.{0} A) := LieModule.ofAssociativeModule
  let : LieRingModule L (ULift.{0} A) := LieRingModule.compLieHom (ULift.{0} A) f
  let : LieModule K L (ULift.{0} A) := LieModule.compLieHom (ULift.{0} A) f
  have hn : IsNilpotent (toEnd K L (ULift.{0} A) x) :=
    LieModule.isNilpotent_toEnd_of_mem_rootSpace (M := ULift.{0} A) H hχ hx
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  have hstep (a : A) :
      (toEnd K L (ULift.{0} A) x) (ULift.up a) = ULift.up ((f x) * a) := by
    rfl
  have hact (m : ℕ) : ∀ a : A,
      ((toEnd K L (ULift.{0} A) x) ^ m) (ULift.up a) = ULift.up ((f x) ^ m * a) := by
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

