import OrbitComplexity.GroupActions.Varieties.AffineMultiplication
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Multiplication of disjoint closed subgroups

The quotient Hopf algebras identify subgroup points with their ambient images. Disjointness
of these images makes multiplication injective, and tensor-product coordinates transfer
this injectivity to the rational points of the affine product.

## Main results

* `GroupActions.quotientMulMap_injective`: injectivity on rational points of the product.
-/

namespace GroupActions

noncomputable section

open TauCeti
open scoped TensorProduct

universe u

variable {K H : Type u} [CommRing K] [CommRing H] [HopfAlgebra K H]

/-- Multiplication of closed subgroups with disjoint rational points is injective on points. -/
theorem quotientMulMap_injective (I J : HopfIdeal K H)
    (h : Disjoint
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H) I (CommAlgCat.of K K))
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H) J (CommAlgCat.of K K))) :
    Function.Injective (fun p : (H ⧸ I.toIdeal) ⊗[K] (H ⧸ J.toIdeal) →ₐ[K] K =>
      p.comp (affineMulMap
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K H) I).hom.toAlgHom
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K H) J).hom.toAlgHom)) := by
  let qI := (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K H) I).hom
  let qJ := (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K H) J).hom
  let eI := MonoidHom.ofInjective
    (f := (CommHopfAlgCat.quotientPointsHom
      (CommHopfAlgCat.of K H) I (CommAlgCat.of K K)).hom)
    (CommHopfAlgCat.quotientPointsHom_injective _ _ _)
  let eJ := MonoidHom.ofInjective
    (f := (CommHopfAlgCat.quotientPointsHom
      (CommHopfAlgCat.of K H) J (CommAlgCat.of K K)).hom)
    (CommHopfAlgCat.quotientPointsHom_injective _ _ _)
  have hprod : Function.Injective (fun p :
      ((H ⧸ I.toIdeal) →ₐ[K] K) × ((H ⧸ J.toIdeal) →ₐ[K] K) =>
      WithConv.toConv (p.1.comp qI.toAlgHom) *
        WithConv.toConv (p.2.comp qJ.toAlgHom)) := by
    intro p q hpq
    have he : (eI (WithConv.toConv p.1), eJ (WithConv.toConv p.2)) =
        (eI (WithConv.toConv q.1), eJ (WithConv.toConv q.2)) :=
      Subgroup.mul_injective_of_disjoint h hpq
    exact Prod.ext
      (WithConv.toConv_injective (eI.injective (congrArg Prod.fst he)))
      (WithConv.toConv_injective (eJ.injective (congrArg Prod.snd he)))
  intro p q hpq
  let e := tensorAlgebraPointsEquiv K (H ⧸ I.toIdeal) (H ⧸ J.toIdeal)
  apply e.injective
  apply hprod
  apply WithConv.ofConv_injective
  have hp := affineMulMap_points qI.toAlgHom qJ.toAlgHom (e p)
  have hq := affineMulMap_points qI.toAlgHom qJ.toAlgHom (e q)
  rw [show (tensorAlgebraPointsEquiv K (H ⧸ I.toIdeal) (H ⧸ J.toIdeal)).symm (e p) = p
    from e.symm_apply_apply p] at hp
  rw [show (tensorAlgebraPointsEquiv K (H ⧸ I.toIdeal) (H ⧸ J.toIdeal)).symm (e q) = q
    from e.symm_apply_apply q] at hq
  exact hp.symm.trans (hpq.trans hq)

end

end GroupActions
