import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.PointConvolutionUnits
import OrbitComplexity.ReductiveGroups.Lie.Roots.SquareZeroCommutator

/-!
# Point Square Zero Commutator

A point commutator is the ring commutator of its
square-zero convolution-linear corrections. -/

noncomputable section
namespace ReductiveGroups

open WithConv
open scoped commutatorElement

variable {K B A : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [CommRing A] [Algebra K A]

/-- The equality is

```lean
toConv (⁅p, q⁆).ofConv.toLinearMap = 1 + (u * v - v * u)
```
-/
theorem point_commutator_of_linear_squareZero
    (p q : WithConv (B →ₐ[K] A))
    (u v : WithConv (B →ₗ[K] A))
    (hp : toConv p.ofConv.toLinearMap = 1 + u)
    (hq : toConv q.ofConv.toLinearMap = 1 + v)
    (hu : u * u = 0) (hv : v * v = 0)
    (huvu : u * v * u = 0) (hvuv : v * u * v = 0) :
    toConv (⁅p, q⁆).ofConv.toLinearMap = 1 + (u * v - v * u) := by
  have hpUnit : pointConvolutionUnits (K := K) (B := B) (A := A) p =
      squareZeroUnit u hu := by
    apply Units.val_injective
    simpa only [pointConvolutionUnits_val, squareZeroUnit_val] using hp
  have hqUnit : pointConvolutionUnits (K := K) (B := B) (A := A) q =
      squareZeroUnit v hv := by
    apply Units.val_injective
    simpa only [pointConvolutionUnits_val, squareZeroUnit_val] using hq
  have hmap := map_commutatorElement
    (pointConvolutionUnits (K := K) (B := B) (A := A)) p q
  rw [hpUnit, hqUnit] at hmap
  have hval := congrArg (fun z : (WithConv (B →ₗ[K] A))ˣ =>
    (z : WithConv (B →ₗ[K] A))) hmap
  exact hval.trans (squareZeroUnit_commutator_val u v hu hv huvu hvuv)

end ReductiveGroups
