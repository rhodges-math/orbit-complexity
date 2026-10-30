import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# Adjoint First Order

The first-order coefficient of adjoint conjugation by a
dual-number tangent point is the tangent Lie bracket. -/

noncomputable section
namespace ReductiveGroups
open WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

private abbrev C := TauCeti.Bialgebra.CounitAlgebra K B K

/-- The dual-number point of the affine group with coordinate Hopf algebra `B` attached to a tangent
vector `h` at the identity; it has first component the counit and `ε`-component `h`. -/
def tangentDualPoint (h : Derivation K B (C (K := K) (B := B))) :
    WithConv (B →ₐ[K] DualNumber (C (K := K) (B := B))) :=
  (TauCeti.derivationMulEquivTangentKer K B K (Multiplicative.ofAdd h)).val

private def scalarInclusion :
    K →ₐ[K] DualNumber (C (K := K) (B := B)) :=
  Algebra.ofId K _

/-- The tangent vector `d`, regarded as a derivation with values in the dual numbers `K[ε]` via the
scalar inclusion `K → K[ε]`. -/
def baseDualDerivation (d : Derivation K B (C (K := K) (B := B))) :
    Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B
      (DualNumber (C (K := K) (B := B)))) :=
  Derivation.mapValue (scalarInclusion (K := K) (B := B)) d

/-- The adjoint action of the dual-number point `tangentDualPoint h` on the tangent vector `d`,
viewed with values in the dual numbers `K[ε]`. -/
def tangentDualAdjoint (h d : Derivation K B (C (K := K) (B := B))) :
    Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B
      (DualNumber (C (K := K) (B := B)))) :=
  Derivation.adDerivation (DualNumber (C (K := K) (B := B)))
    (tangentDualPoint h) (baseDualDerivation d)

private theorem tangentDualPoint_inv (h : Derivation K B (C (K := K) (B := B))) :
    (tangentDualPoint h)⁻¹ = tangentDualPoint (-h) := by
  simp [tangentDualPoint]

/-- The equality is

```lean
TrivSqZeroExt.fst ((tangentDualPoint h).ofConv a) =
      algebraMap B (C (K := K) (B := B)) a
```
-/
theorem tangentDualPoint_fst (h : Derivation K B (C (K := K) (B := B)))
    (a : B) :
    TrivSqZeroExt.fst ((tangentDualPoint h).ofConv a) =
      algebraMap B (C (K := K) (B := B)) a := by
  exact TauCeti.derivationMulEquivTangentKer_apply_fst
    (Multiplicative.ofAdd h) a

/-- The equality is

```lean
TrivSqZeroExt.snd ((tangentDualPoint h).ofConv a) = h a
```
-/
theorem tangentDualPoint_snd (h : Derivation K B (C (K := K) (B := B)))
    (a : B) :
    TrivSqZeroExt.snd ((tangentDualPoint h).ofConv a) = h a := by
  exact TauCeti.derivationMulEquivTangentKer_apply_snd
    (Multiplicative.ofAdd h) a

private theorem baseDualDerivation_fst (d : Derivation K B (C (K := K) (B := B)))
    (a : B) : TrivSqZeroExt.fst (baseDualDerivation d a) = d a := by
  change TrivSqZeroExt.fst
    (Derivation.mapValue (scalarInclusion (K := K) (B := B)) d a) = d a
  rw [Derivation.mapValue_apply]
  change TrivSqZeroExt.fst (TrivSqZeroExt.inl (d a)) = d a
  simp

private theorem baseDualDerivation_snd (d : Derivation K B (C (K := K) (B := B)))
    (a : B) : TrivSqZeroExt.snd (baseDualDerivation d a) = 0 := by
  change TrivSqZeroExt.snd
    (Derivation.mapValue (scalarInclusion (K := K) (B := B)) d a) = 0
  rw [Derivation.mapValue_apply]
  change TrivSqZeroExt.snd (TrivSqZeroExt.inl (d a)) = 0
  simp

private def convFst (f : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    WithConv (B →ₗ[K] (C (K := K) (B := B))) :=
  toConv ((TrivSqZeroExt.fstHom K _ _).toLinearMap.comp f.ofConv)

private def convSnd (f : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    WithConv (B →ₗ[K] (C (K := K) (B := B))) :=
  toConv ((TrivSqZeroExt.sndHom _ _).restrictScalars K |>.comp f.ofConv)

private theorem convFst_mul
    (f g : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    convFst (f * g) = convFst f * convFst g := by
  exact congrArg toConv
    (LinearMap.algHom_comp_convMul_distrib (TrivSqZeroExt.fstHom K _ _) f g)

private theorem convSnd_mul
    (f g : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    convSnd (f * g) = convFst f * convSnd g + convSnd f * convFst g := by
  exact congrArg toConv (WithConv.snd_comp_convMul f g)

private theorem convFst_point (h : Derivation K B (C (K := K) (B := B))) :
    convFst (toConv (tangentDualPoint h).ofConv.toLinearMap) = 1 := by
  ext a
  exact tangentDualPoint_fst h a

private theorem convSnd_point (h : Derivation K B (C (K := K) (B := B))) :
    convSnd (toConv (tangentDualPoint h).ofConv.toLinearMap) =
      toConv (↑h : B →ₗ[K] C (K := K) (B := B)) := by
  ext a
  exact tangentDualPoint_snd h a

private theorem convFst_base (d : Derivation K B (C (K := K) (B := B))) :
    convFst (toConv (baseDualDerivation d).toLinearMap) =
      toConv (↑d : B →ₗ[K] C (K := K) (B := B)) := by
  ext a
  exact baseDualDerivation_fst d a

private theorem convSnd_base (d : Derivation K B (C (K := K) (B := B))) :
    convSnd (toConv (baseDualDerivation d).toLinearMap) = 0 := by
  ext a
  exact baseDualDerivation_snd d a

private theorem convFst_invpoint (h : Derivation K B (C (K := K) (B := B))) :
    convFst (toConv ((tangentDualPoint h)⁻¹).ofConv.toLinearMap) = 1 := by
  rw [tangentDualPoint_inv]
  exact convFst_point (-h)

private theorem convSnd_invpoint (h : Derivation K B (C (K := K) (B := B))) :
    convSnd (toConv ((tangentDualPoint h)⁻¹).ofConv.toLinearMap) =
      -toConv (↑h : B →ₗ[K] C (K := K) (B := B)) := by
  rw [tangentDualPoint_inv, convSnd_point]
  rfl

/-- The first-order coefficient of adjoint conjugation by the
dual-number point associated to `h` is the tangent Lie bracket. -/
theorem tangentDualAdjoint_snd
    (h d : Derivation K B (C (K := K) (B := B))) (a : B) :
    TrivSqZeroExt.snd (tangentDualAdjoint h d a) = ⁅h, d⁆ a := by
  let H : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B))) :=
    toConv (tangentDualPoint h).ofConv.toLinearMap
  let D : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B))) :=
    toConv (baseDualDerivation d).toLinearMap
  let I : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B))) :=
    toConv ((tangentDualPoint h)⁻¹).ofConv.toLinearMap
  let hc : WithConv (B →ₗ[K] C (K := K) (B := B)) := toConv (↑h)
  let dc : WithConv (B →ₗ[K] C (K := K) (B := B)) := toConv (↑d)
  have heq : convSnd (H * D * I) = hc * dc - dc * hc := by
    rw [convSnd_mul, convFst_mul, convSnd_mul]
    rw [show convFst H = 1 from convFst_point h,
      show convSnd H = hc from convSnd_point h,
      show convFst D = dc from convFst_base d,
      show convSnd D = 0 from convSnd_base d,
      show convFst I = 1 from convFst_invpoint h,
      show convSnd I = -hc from convSnd_invpoint h]
    simp only [one_mul, mul_one, zero_add, mul_zero]
    have hneg : dc * -hc = -(dc * hc) := mul_neg dc hc
    rw [hneg]
    abel
  have hbracket : (hc * dc - dc * hc).ofConv a = ⁅h,d⁆ a := by
    have hh := Derivation.coe_bracket h d
    have ha := DFunLike.congr_fun hh a
    change (hc * dc).ofConv a - (dc * hc).ofConv a = ⁅h,d⁆ a
    exact ha.symm
  rw [← hbracket, ← heq]
  change TrivSqZeroExt.snd ((H * D * I).ofConv a) =
    (convSnd (H * D * I)).ofConv a
  rfl

end ReductiveGroups
