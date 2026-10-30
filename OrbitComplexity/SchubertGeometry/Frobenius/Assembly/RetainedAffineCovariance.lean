import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorCovariance
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Affine covariance with the retained prior frame

The prior Cartier map contributes its full frame-transition factor before
the affine fibre substitution is made. Both identifications are applied to
the same retained coefficient diagram and the same prior line map.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting Polynomial

noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveCartier

open private retainedChartRange retainedCoordinateIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

private theorem affine_input {A : Type u} [CommRing A] (p : ℕ)
    (a : Aˣ) (b g : A) (Q : Polynomial A) :
    C (g * (↑(a⁻¹) : A) ^ (p - 1)) * Q.comp (C (a : A) * X + C b) =
      C ((↑(a⁻¹) : A) ^ (p - 1)) *
        (C g * Q).comp (C (a : A) * X + C b) := by
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.C_mul]
  ac_rfl

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
    {R : Type u} [CommRing R] [Algebra K R]
    {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
    (N : J ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)

/-- Under an affine fibre coordinate change, the retained prior trace includes
both its prior-frame scalar and the inverse affine slope to power p minus one. -/
theorem retainedAffinePriorTrace_map
    (base : cG.pt.left ⟶ Spec (.of K)) (L : cG.pt.left.Modules)
    (Θ : frobeniusRestriction K p base L ⟶ SheafOfModules.unit cG.pt.left.ringCatSheaf)
    {s t : J} (f : s ⟶ t)
    (e : Γ(L, retainedChartRange N cG hcG s))
    (e' : Γ(L, retainedChartRange N cG hcG t))
    (g : Γ(cG.pt.left, retainedChartRange N cG hcG t))
    (hle : retainedChartRange N cG hcG t ≤ retainedChartRange N cG hcG s)
    (he : L.presheaf.map (homOfLE hle).op e = g • e')
    (hp : 0 < p) (a : (N.obj t)ˣ) (b : N.obj t) (Q : Polynomial (N.obj s)) :
    letI : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    letI : Algebra K (N.obj t) :=
      ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
    let g' := (retainedCoordinateIso N cG hcG t).hom g
    polynomialTraceOfOperator (K := K)
        (retainedTwistedPriorOperator N cG hcG base L Θ t e')
        (C (g' * (↑(a⁻¹) : N.obj t) ^ (p - 1)) *
          (Polynomial.map (N.map f).hom.toRingHom Q).comp (C (a : N.obj t) * X + C b)) =
      (Polynomial.map (N.map f).hom.toRingHom
        (polynomialTraceOfOperator (K := K)
          (retainedTwistedPriorOperator N cG hcG base L Θ s e) Q)).comp
            (C (a : N.obj t) * X + C b) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let : Algebra K (N.obj t) :=
    ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
  let g' := (retainedCoordinateIso N cG hcG t).hom g
  let ψ := retainedTwistedPriorOperator N cG hcG base L Θ t e'
  let Q' := Polynomial.map (N.map f).hom.toRingHom Q
  let F := C (a : N.obj t) * X + C b
  have hprior := retainedTwistedPriorTrace_map N cG hcG base L Θ f e e' g hle he Q
  have hcov := polynomialTraceOfOperator_affine (K := K) ψ hp a b (C g' * Q')
  have hinput := affine_input p a b g' Q'
  exact (congrArg (polynomialTraceOfOperator (K := K) ψ) hinput).trans
    (hcov.trans (congrArg (fun P : Polynomial (N.obj t) => P.comp F) hprior))

end SchubertGeometry.ProjectiveCartier
