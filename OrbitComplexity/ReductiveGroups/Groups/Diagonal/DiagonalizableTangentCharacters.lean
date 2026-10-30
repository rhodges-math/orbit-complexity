import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferential
import TauCeti.RingTheory.Derivation.DualNumber

/-!
# Diagonalizable Tangent Characters

Tangent vectors separating characters of a diagonalizable group. -/

noncomputable section
namespace ReductiveGroups
open TrivSqZeroExt

variable {K M : Type*} [Field K] [CommGroup M]

private def dualCharacter (ψ : M →* Multiplicative K) : M →* DualNumber K where
  toFun m := inl 1 + inr (ψ m).toAdd
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [fst_mul, snd_mul, map_mul, add_comm]

private def dualCharacterAlgHom (ψ : M →* Multiplicative K) :
    MonoidAlgebra K M →ₐ[K] DualNumber K :=
  MonoidAlgebra.lift K (DualNumber K) M (dualCharacter ψ)

private theorem dualCharacterAlgHom_fst (ψ : M →* Multiplicative K) :
    (fstHom K K K).comp (dualCharacterAlgHom ψ) =
      Bialgebra.counitAlgHom K (MonoidAlgebra K M) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp [dualCharacterAlgHom, dualCharacter]
  · ext

/-- A tangent vector obtained by lifting an additive functional on
the character group to a dual-number-valued point. -/
def diagonalizableTangentOfAdditive (ψ : M →* Multiplicative K) :
    Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K) := by
  let φ : MonoidAlgebra K M →ₐ[K] DualNumber K := dualCharacterAlgHom ψ
  have hφ : (fstHom K K K).comp φ =
      Bialgebra.counitAlgHom K (MonoidAlgebra K M) :=
    dualCharacterAlgHom_fst ψ
  exact (TauCeti.derivationToDualNumberEquivLift K (MonoidAlgebra K M)
    (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)).symm ⟨φ, hφ⟩

/-- The equality is

```lean
characterDifferential (K := K) m (diagonalizableTangentOfAdditive ψ) =
      (ψ m).toAdd
```
-/
theorem CharacterDifferential.of_additive_tangent
    (ψ : M →* Multiplicative K) (m : M) :
    characterDifferential (K := K) m (diagonalizableTangentOfAdditive ψ) =
      (ψ m).toAdd := by
  change (diagonalizableTangentOfAdditive ψ)
    (MonoidAlgebra.single m 1) = (ψ m).toAdd
  unfold diagonalizableTangentOfAdditive
  rw [TauCeti.derivationToDualNumberEquivLift_symm_apply]
  change snd (dualCharacterAlgHom ψ (MonoidAlgebra.single m 1)) = _
  rw [dualCharacterAlgHom, MonoidAlgebra.lift_single, one_smul]
  change snd (inl 1 + inr (ψ m).toAdd) = _
  simp

variable {ι : Type*}

private def latticeCoordinateCharacter (i : ι) :
    Multiplicative (ι →₀ ℤ) →* Multiplicative K where
  toFun m := Multiplicative.ofAdd ((m.toAdd i : ℤ) : K)
  map_one' := by simp
  map_mul' a b := by simp [Finsupp.add_apply, Int.cast_add]

/-- A coordinate tangent vector evaluates a lattice character at that
coordinate, viewed in the field. -/
theorem characterDifferential_latticeCoordinate (i : ι)
    (α : Multiplicative (ι →₀ ℤ)) :
    characterDifferential (K := K) α
      (diagonalizableTangentOfAdditive (latticeCoordinateCharacter (K := K) i)) =
        ((α.toAdd i : ℤ) : K) := by
  exact CharacterDifferential.of_additive_tangent _ _

/-- A nonidentity character of a free integer lattice has nonzero
differential at the identity in characteristic zero. -/
theorem characterDifferential_ne_zero_of_ne_one [CharZero K]
    (α : Multiplicative (ι →₀ ℤ)) (hα : α ≠ 1) :
    characterDifferential (K := K) α ≠ 0 := by
  have hne : α.toAdd ≠ 0 := by
    intro hz
    apply hα
    cases α with
    | ofAdd a =>
      change a = 0 at hz
      subst a
      rfl
  obtain ⟨i, hi⟩ : ∃ i, α.toAdd i ≠ 0 := by
    by_contra! hn
    apply hne
    ext i
    exact hn i
  intro hzero
  have hv := congrArg (fun f : Derivation K (MonoidAlgebra K
      (Multiplicative (ι →₀ ℤ)))
      (TauCeti.Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K) →ₗ[K] K =>
      f (diagonalizableTangentOfAdditive (latticeCoordinateCharacter (K := K) i))) hzero
  rw [characterDifferential_latticeCoordinate, LinearMap.zero_apply] at hv
  exact (Int.cast_ne_zero.mpr hi) hv

end ReductiveGroups
