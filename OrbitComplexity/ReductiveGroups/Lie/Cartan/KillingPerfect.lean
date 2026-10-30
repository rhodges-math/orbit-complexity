import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Abelian

/-!
# Killing Perfect

A finite-dimensional Lie algebra with nondegenerate Killing form is
perfect, including in the characteristics where this hypothesis makes sense. -/

noncomputable section
namespace ReductiveGroups

variable {K S : Type*} [Field K] [LieRing S] [LieAlgebra K S]
  [Module.Finite K S] [LieAlgebra.IsKilling K S]

/-- The equality is

```lean
LieAlgebra.derivedSeries K S 1 = ⊤
```
-/
theorem killing_derivedSeries_one_eq_top :
    LieAlgebra.derivedSeries K S 1 = ⊤ := by
  have hsemi : LieAlgebra.IsSemisimple K S := inferInstance
  apply top_unique
  rw [← LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := K) (L := S)]
  apply sSup_le
  intro I hI
  have hnon : ¬IsLieAbelian I :=
    LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI
  rw [← lie_eq_self_of_isAtom_of_nonabelian I hI hnon]
  exact LieSubmodule.mono_lie le_top le_top

variable {A : Type*} [LieRing A] [LieAlgebra K A] [IsLieAbelian A]

/-- A perfect Killing Lie algebra has no nonzero Lie homomorphism to an
abelian Lie algebra. -/
theorem killing_lieHom_abelian_eq_zero (f : S →ₗ⁅K⁆ A) : f = 0 := by
  apply LieHom.ext
  intro x
  have hx : x ∈ LieAlgebra.derivedSeries K S 1 := by
    rw [killing_derivedSeries_one_eq_top]
    exact LieSubmodule.mem_top x
  have hmap : f x ∈ (LieAlgebra.derivedSeries K S 1).map f :=
    LieIdeal.mem_map hx
  have hle := LieIdeal.derivedSeries_map_le (f := f) 1
  have habel : LieAlgebra.derivedSeries K A 1 = ⊥ := by
    change ⁅(⊤ : LieIdeal K A), ⊤⁆ = ⊥
    have htop : IsLieAbelian (⊤ : LieIdeal K A) :=
      (⊤ : LieIdeal K A).incl_injective.isLieAbelian inferInstance
    exact (LieSubmodule.lie_abelian_iff_lie_self_eq_bot
      (⊤ : LieIdeal K A)).mp htop
  have hz : f x ∈ (⊥ : LieIdeal K A) := by
    rw [← habel]
    exact hle hmap
  change f x = 0
  simpa using hz

end ReductiveGroups
