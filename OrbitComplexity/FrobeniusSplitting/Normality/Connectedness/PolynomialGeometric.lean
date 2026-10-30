import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.PolynomialBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.PolynomialConnected
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Geometric connectedness from an arithmetic polynomial contraction

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace FrobeniusSplitting

universe u

/-- An arithmetic polynomial contraction with a scalar origin gives connected
geometric fibres of its original structural map. -/
theorem geomConnected_of_polynomial {R C : Type u} [CommRing R] [CommRing C]
    [Algebra R C] (σ : C →ₐ[R] Polynomial C) (ε : C →ₐ[R] R)
    (hOne : ∀ c : C, (σ c).eval 1 = c)
    (hZero : ∀ c : C, (σ c).eval 0 = algebraMap R C (ε c)) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
  constructor
  intro L hL y Z fst snd h
  let r : R →+* L := (Spec.preimage y).hom
  let : Algebra R L := r.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom r) = y := Spec.map_preimage y
  have ht : IsPullback snd fst
      (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
    simpa only [hy] using h.flip
  let e : Z ≅ Spec (.of (L ⊗[R] C)) :=
    ht.isoPullback ≪≫ pullbackSpecIso R L C
  let : ConnectedSpace (Spec (.of (L ⊗[R] C))) :=
    spec_connected_of_polynomial (polynomialTensorContraction (A := L) σ)
      (polynomialTensorOrigin (A := L) ε)
      (polynomialTensorContraction_one σ hOne)
      (polynomialTensorContraction_zero σ ε hZero)
  exact (Scheme.homeoOfIso e).connectedSpace_iff.mpr inferInstance

end FrobeniusSplitting
