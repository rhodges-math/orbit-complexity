import OrbitComplexity.ReductiveGroups.Groups.Tangents.AdjointDifferentialNaturality
import Mathlib.Algebra.BigOperators.Ring.List
import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# Adjoint Representation

The ordinary-point adjoint representation and its product order. -/

noncomputable section
namespace ReductiveGroups
open WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The original affine group's adjoint representation on its tangent
Lie algebra, expressed on ordinary field-valued points. -/
def affineGroupAdjointRepresentation :
    Representation K (WithConv (B →ₐ[K] K))
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :=
  (Derivation.adRepresentation K).comp
    (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm.toMonoidHom

/-- The equality is

```lean
affineGroupAdjointRepresentation g d =
      Derivation.adDerivation K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g) d
```
-/
@[simp]
theorem affineGroupAdjointRepresentation_apply
    (g : WithConv (B →ₐ[K] K))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    affineGroupAdjointRepresentation g d =
      Derivation.adDerivation K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g) d := by
  simp [affineGroupAdjointRepresentation]

/-- The adjoint endomorphism of an ordered finite product of original
group points is the endomorphism product in that same order. -/
theorem AffineGroupAdjointRepresentation.list_prod
    (gs : List (WithConv (B →ₐ[K] K))) :
    affineGroupAdjointRepresentation gs.prod =
      (gs.map affineGroupAdjointRepresentation).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [List.prod_cons, map_mul, ih]

/-- Applying the ordered product acts by successive adjoints in the
reverse list order, because endomorphism multiplication is composition. -/
theorem AffineGroupAdjointRepresentation.list_prod_apply
    (gs : List (WithConv (B →ₐ[K] K)))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    affineGroupAdjointRepresentation gs.prod d =
      gs.reverse.foldl
        (fun z g => Derivation.adDerivation K
          ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g) z) d := by
  rw [AffineGroupAdjointRepresentation.list_prod]
  induction gs with
  | nil => simp
  | cons g gs ih =>
      simp [List.reverse_cons, List.foldl_append, Module.End.mul_apply,
        affineGroupAdjointRepresentation_apply, ih]

/-- The inverse of a finite point product acts by the adjoint
endomorphisms of the inverse factors in reversed product order. -/
theorem AffineGroupAdjointRepresentation.list_prod_inv
    (gs : List (WithConv (B →ₐ[K] K))) :
    affineGroupAdjointRepresentation (gs.prod)⁻¹ =
      ((gs.reverse.map Inv.inv).map affineGroupAdjointRepresentation).prod := by
  have h (l : List (WithConv (B →ₐ[K] K))) :
      (l.prod)⁻¹ = (l.reverse.map Inv.inv).prod := by
    induction l with
    | nil => simp
    | cons g l ih =>
        simp [List.prod_cons, List.reverse_cons, List.map_append,
          List.prod_append, mul_inv_rev, ih]
  rw [h]
  exact AffineGroupAdjointRepresentation.list_prod _

end ReductiveGroups

open TauCeti
open scoped TensorProduct
noncomputable section
universe u
namespace ReductiveGroups
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]

/-- The adjoint comodule on the counit-valued tangent derivations. -/
@[instance_reducible]
def affineGroupAdjointComodule :
    Comodule K B (Derivation K B (Bialgebra.CounitAlgebra K B K)) :=
  letI := Derivation.adjointComodule (R := K) (H := B)
  Comodule.Transport (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K))

private theorem hom_basePoints {H V W : Type u} [CommRing H] [HopfAlgebra K H]
    [AddCommGroup V] [Module K V] [Comodule K H V]
    [AddCommGroup W] [Module K W] [Comodule K H W]
    (f : Comodule.Hom K H V W) (g : WithConv (H →ₐ[K] K)) (v : V) :
    f (Comodule.basePointsRepresentation (H := H) V g v) =
      Comodule.basePointsRepresentation (H := H) W g (f v) := by
  change f.toLinearMap (Comodule.basePointsRepresentation (H := H) V g v) =
    Comodule.basePointsRepresentation (H := H) W g (f.toLinearMap v)
  have ht (x : K ⊗[K] V) :
      f.toLinearMap (TensorProduct.lid K V x) =
        TensorProduct.lid K W (f.toLinearMap.baseChange K x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a v => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Comodule.basePointsRepresentation_apply, ht,
    Comodule.basePointsRepresentation_apply]
  have h := LinearMap.congr_fun (Comodule.baseChange_comp_endOfPoint f g.ofConv)
    (1 ⊗ₜ[K] v)
  exact congrArg (TensorProduct.lid K W)
    (by simpa only [LinearMap.comp_apply, LinearMap.baseChange_tmul] using h)

private theorem cotangent_one
    (x : Module.Dual K (Bialgebra.CotangentSpace K B)) :
    Derivation.tangentScalarExtensionEquiv (R := K) (A := B) (B := K)
        (1 ⊗ₜ[K] x) =
      Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K) x := by
  apply Derivation.ext
  intro a
  simp only [Derivation.tangentScalarExtensionEquiv_tmul_apply,
    Algebra.algebraMap_self, RingHom.id_apply, one_mul]
  exact (Derivation.cotangentLinearEquiv_apply_apply x a).symm

private theorem cotangent_points (g : WithConv (B →ₐ[K] K))
    (x : Module.Dual K (Bialgebra.CotangentSpace K B)) :
    letI := Derivation.adjointComodule (R := K) (H := B)
    Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)
        (Comodule.basePointsRepresentation (H := B) _ g x) =
      affineGroupAdjointRepresentation g
        (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K) x) := by
  let := Derivation.adjointComodule (R := K) (H := B)
  have hb : Comodule.endOfPoint
      (Module.Dual K (Bialgebra.CotangentSpace K B)) g.ofConv
        (1 ⊗ₜ[K] x) =
      1 ⊗ₜ[K] Comodule.basePointsRepresentation (H := B) _ g x := by
    rw [Comodule.endOfPoint_tmul, one_smul]
    exact Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation g x
  have h := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (CommAlgCat.of K K) g (1 ⊗ₜ[K] x)
  rw [hb, cotangent_one, cotangent_one] at h
  have hpoint : Derivation.pointInCounitAlgebra K g =
      (Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g := rfl
  rw [hpoint] at h
  simpa only [affineGroupAdjointRepresentation_apply] using h

/-- The adjoint comodule evaluates to the adjoint representation on field-valued points. -/
theorem affineGroupAdjointComodule_points (g : WithConv (B →ₐ[K] K)) :
    letI := affineGroupAdjointComodule (K := K) (B := B)
    Comodule.basePointsRepresentation (H := B) (Derivation K B (Bialgebra.CounitAlgebra K B K)) g =
      affineGroupAdjointRepresentation g := by
  let := Derivation.adjointComodule (R := K) (H := B)
  let e := Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)
  let : Comodule K B (Derivation K B (Bialgebra.CounitAlgebra K B K)) := Comodule.Transport e
  apply LinearMap.ext
  intro d
  have hn := hom_basePoints (Comodule.transportToHom (C := B) e)
    g (e.symm d)
  change e (Comodule.basePointsRepresentation (H := B) _ g (e.symm d)) =
    Comodule.basePointsRepresentation (H := B) (Derivation K B (Bialgebra.CounitAlgebra K B K)) g
      (e (e.symm d)) at hn
  rw [LinearEquiv.apply_symm_apply] at hn
  have hc := cotangent_points g (e.symm d)
  exact hn.symm.trans (by simpa only [e, LinearEquiv.apply_symm_apply] using hc)


end ReductiveGroups
