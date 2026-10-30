import Mathlib.Algebra.Lie.Weights.IsSimple

/-! # Cartan detection of Lie ideals -/

noncomputable section

namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u v
variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- An ideal in a split Killing Lie algebra is detected by its Cartan intersection. -/
theorem lieIdeal_eq_bot_of_cartan_inf (I : LieIdeal K L)
    (hI : I.restr H ⊓ H.toLieSubmodule = ⊥) : I = ⊥ := by
  have hroot (a : H.root) : ¬ rootSpace H a.val ≤ I.restr H := by
    intro ha
    have hc : (coroot a.val : L) ∈ I.restr H ⊓ H.toLieSubmodule :=
      ⟨I.corootSubmodule_le ha (coe_coroot_mem_corootSubmodule a.val),
        (coroot a.val).property⟩
    have hz : (coroot a.val : L) = 0 := by simpa only [hI, LieSubmodule.mem_bot] using hc
    have hz' : coroot a.val = 0 := Subtype.ext hz
    exact H.isNonZero_coe_root a (coroot_eq_zero_iff.mp hz')
  have hi : I.restr H = ⊥ := by
    rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace I, hI]
    simp [hroot]
  ext x
  change x ∈ I.restr H ↔ x ∈ (⊥ : LieSubmodule K H L)
  rw [hi]

end ReductiveGroups
