import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointFirstOrder
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Square Zero Tangent Point

Tangent points over arbitrary square-zero parameters. -/

noncomputable section
namespace ReductiveGroups

open WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

private abbrev C := TauCeti.Bialgebra.CounitAlgebra K B K

/-- Evaluate the dual-number infinitesimal at an arbitrary square-zero
element of a commutative value algebra. -/
def squareZeroDualEval {A : Type*} [CommRing A] [Algebra K A]
    (a : A) (ha : a * a = 0) : DualNumber (C (K := K) (B := B)) →ₐ[K] A := by
  let f : C (K := K) (B := B) →ₐ[K] A :=
    (Algebra.ofId K A).comp
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).toAlgHom
  exact DualNumber.lift ⟨(f, a), ⟨ha, fun r => mul_comm a (f r)⟩⟩

/-- The point obtained by evaluating a tangent dual-number point
at a square-zero parameter in any commutative value algebra. -/
def squareZeroTangentPoint
    (d : Derivation K B (C (K := K) (B := B)))
    {A : Type*} [CommRing A] [Algebra K A]
    (a : A) (ha : a * a = 0) : WithConv (B →ₐ[K] A) :=
  TauCeti.AlgHom.mapValue (squareZeroDualEval (K := K) (B := B) a ha)
    (tangentDualPoint d)

/-- The equality is

```lean
(squareZeroTangentPoint d a ha).ofConv b =
      algebraMap K A (Coalgebra.counit b) +
        a * algebraMap K A
          (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K (d b))
```
-/
theorem squareZeroTangentPoint_apply
    (d : Derivation K B (C (K := K) (B := B)))
    {A : Type*} [CommRing A] [Algebra K A]
    (a : A) (ha : a * a = 0) (b : B) :
    (squareZeroTangentPoint d a ha).ofConv b =
      algebraMap K A (Coalgebra.counit b) +
        a * algebraMap K A
          (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K (d b)) := by
  rw [squareZeroTangentPoint, TauCeti.AlgHom.mapValue_apply]
  change squareZeroDualEval (K := K) (B := B) a ha ((tangentDualPoint d).ofConv b) = _
  rw [show squareZeroDualEval (K := K) (B := B) a ha =
      DualNumber.lift ⟨((Algebra.ofId K A).comp
        (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).toAlgHom, a),
        ⟨ha, fun r => mul_comm a _⟩⟩ from rfl,
      DualNumber.lift_apply_apply,
      tangentDualPoint_fst, tangentDualPoint_snd,
      TauCeti.Bialgebra.CounitAlgebra.algebraMap_apply]
  change ((Algebra.ofId K A).comp
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).toAlgHom)
      (algebraMap K K (Coalgebra.counit b)) +
      ((Algebra.ofId K A).comp
        (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).toAlgHom) (d b) * a = _
  simp only [AlgHom.comp_apply,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Algebra.ofId_apply]
  simp [mul_comm]
  exact Algebra.ofId_apply (R := K) (A := A) (Coalgebra.counit b : K)

/-- Square-zero tangent points commute with extension of the value algebra. -/
theorem squareZeroTangentPoint_map
    (d : Derivation K B (C (K := K) (B := B)))
    {A A' : Type*} [CommRing A] [Algebra K A]
    [CommRing A'] [Algebra K A']
    (f : A →ₐ[K] A') (a : A) (ha : a * a = 0) :
    TauCeti.AlgHom.mapValue f (squareZeroTangentPoint d a ha) =
      squareZeroTangentPoint d (f a) (by rw [← map_mul, ha, map_zero]) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  rw [TauCeti.AlgHom.mapValue_apply]
  change f ((squareZeroTangentPoint d a ha).ofConv b) = _
  rw [squareZeroTangentPoint_apply, squareZeroTangentPoint_apply,
    map_add, map_mul]
  rw [f.commutes, f.commutes]

/-- Inverting a square-zero tangent point negates its tangent vector. -/
theorem squareZeroTangentPoint_inv
    (d : Derivation K B (C (K := K) (B := B)))
    {A : Type*} [CommRing A] [Algebra K A]
    (a : A) (ha : a * a = 0) :
    (squareZeroTangentPoint d a ha)⁻¹ = squareZeroTangentPoint (-d) a ha := by
  let φ : WithConv (B →ₐ[K] DualNumber (C (K := K) (B := B))) →*
      WithConv (B →ₐ[K] A) :=
    TauCeti.AlgHom.mapValue (squareZeroDualEval (K := K) (B := B) a ha)
  change (φ (tangentDualPoint d))⁻¹ = φ (tangentDualPoint (-d))
  rw [← map_inv φ]
  simp [tangentDualPoint]

end ReductiveGroups
