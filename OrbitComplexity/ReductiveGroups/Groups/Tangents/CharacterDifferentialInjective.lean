import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentCharacters

/-!
# Character Differential Injective

Distinct free-lattice characters have distinct differentials in
characteristic zero, also after identifying a closed diagonalizable
subgroup with its tangent image. -/

noncomputable section
namespace ReductiveGroups

variable {K ι : Type*} [Field K] [CharZero K]

/-- The equality is

```lean
Function.Injective (characterDifferential (K := K)
      (M := Multiplicative (ι →₀ ℤ)))
```
-/
theorem characterDifferential_injective :
    Function.Injective (characterDifferential (K := K)
      (M := Multiplicative (ι →₀ ℤ))) := by
  intro α β h
  by_contra hne
  have hq : α * β⁻¹ ≠ 1 := by
    intro hq
    apply hne
    calc
      α = (α * β⁻¹) * β := by simp
      _ = β := by rw [hq, one_mul]
  have hz : characterDifferential (K := K) (α * β⁻¹) = 0 := by
    rw [characterDifferential_mul, characterDifferential_inv, h,
      add_neg_cancel]
  exact (characterDifferential_ne_zero_of_ne_one (K := K) _ hq) hz

variable {B : Type*} [CommRing B] [HopfAlgebra K B]

/-- The equality is

```lean
Function.Injective (fun α : Multiplicative (ι →₀ ℤ) =>
      characterDifferentialOnImage π hπ α)
```
-/
theorem characterDifferentialOnImage_injective
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    Function.Injective (fun α : Multiplicative (ι →₀ ℤ) =>
      characterDifferentialOnImage π hπ α) := by
  intro α β h
  apply characterDifferential_injective (K := K)
  ext d
  have hv := LinearMap.congr_fun h (diagonalizableTangentEquivImage π hπ d)
  simpa only [characterDifferentialOnImage_apply_equiv] using hv

end ReductiveGroups
