import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Character Differential

Differentials of characters on a diagonalizable group. -/

noncomputable section
namespace ReductiveGroups

variable {K M : Type*} [Field K] [CommGroup M]

/-- The differential of a character, evaluated on the tangent space
of the diagonalizable group with coordinate algebra `K[M]`. -/
def characterDifferential (α : M) :
    Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K) →ₗ[K] K where
  toFun h := TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K
    (h (MonoidAlgebra.single α 1))
  map_add' h k := by simp only [Derivation.add_apply, map_add]
  map_smul' c h := by
    exact TauCeti.algEquivSelf_derivation_smul_apply c h _

/-- The equality is

```lean
characterDifferential (K := K) α h =
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K
        (h (MonoidAlgebra.single α 1))
```
-/
@[simp] theorem characterDifferential_apply (α : M)
    (h : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) :
    characterDifferential (K := K) α h =
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K
        (h (MonoidAlgebra.single α 1)) := rfl

/-- The equality is

```lean
characterDifferential (K := K) (1 : M) = 0
```
-/
@[simp] theorem characterDifferential_one :
    characterDifferential (K := K) (1 : M) = 0 := by
  ext h
  change TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K
    (h (MonoidAlgebra.single 1 1)) = 0
  rw [← MonoidAlgebra.one_def, Derivation.map_one_eq_zero, map_zero]

/-- Multiplication of characters differentiates to addition of functionals. -/
theorem characterDifferential_mul (α β : M) :
    characterDifferential (K := K) (α * β) =
      characterDifferential α + characterDifferential β := by
  ext h
  simp only [LinearMap.add_apply, characterDifferential_apply]
  rw [show MonoidAlgebra.single (α * β) (1 : K) =
    MonoidAlgebra.single α 1 * MonoidAlgebra.single β 1 by
      rw [MonoidAlgebra.single_mul_single, one_mul]]
  rw [Derivation.leibniz, map_add,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul]
  simp only [MonoidAlgebra.counit_single, Bialgebra.counit_one, map_one, one_mul]
  exact add_comm _ _

/-- The equality is

```lean
characterDifferential (K := K) α⁻¹ = -characterDifferential α
```
-/
@[simp] theorem characterDifferential_inv (α : M) :
    characterDifferential (K := K) α⁻¹ = -characterDifferential α := by
  have h := characterDifferential_mul (K := K) α⁻¹ α
  rw [inv_mul_cancel, characterDifferential_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The tangent Lie algebra of a diagonalizable group is abelian, using its
convolution bracket. -/
theorem diagonalizableTangent_lie_eq_zero
    (h d : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) :
    ⁅h, d⁆ = 0 := by
  ext a
  have hbr := DFunLike.congr_fun (Derivation.coe_bracket h d) a
  have hcomm : WithConv.toConv h.toLinearMap * WithConv.toConv d.toLinearMap =
      WithConv.toConv d.toLinearMap * WithConv.toConv h.toLinearMap := mul_comm _ _
  rw [hcomm, sub_self] at hbr
  exact hbr

end ReductiveGroups
