import OrbitComplexity.FrobeniusSplitting.Normality.ModelImages
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Batteries.Tactic.Lint

/-!
# Cartesian comparisons for affine arithmetic models

A tensor-product comparison isomorphism identifies an affine scheme with the base change
of its model. Its projection formulas give the coefficient and model-coordinate morphisms.
Polynomial coefficient spectra retain their zero sections and finite-presentation properties.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

section AffineModels

variable {R K M A : Type u} [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra R K] [Algebra R M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- A scalar-extension comparison identifies the affine algebra with the base-changed model. -/
noncomputable def affineModelIso (e : K ⊗[R] M ≃ₐ[K] A) :
    Spec (.of A) ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R M))) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ (pullbackSpecIso R K M).symm

omit [Algebra R A] [IsScalarTower R K A] in
/-- The comparison isomorphism respects the coefficient-field projection. -/
theorem affineModelIso_fst (e : K ⊗[R] M ≃ₐ[K] A) :
    (affineModelIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R K M).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply congrArg CommRingCat.ofHom
  ext k
  exact e.commutes k

/-- The comparison isomorphism respects the model-coordinate projection. -/
theorem affineModelIso_snd (e : K ⊗[R] M ≃ₐ[K] A) :
    (affineModelIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (tensorImageHom e).toRingHom) := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R K M).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A scalar-extension comparison gives a cartesian square of affine schemes. -/
theorem isPullback_affineModel (e : K ⊗[R] M ≃ₐ[K] A) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (tensorImageHom e).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R M))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (affineModelIso e)
    (affineModelIso_fst e) (affineModelIso_snd e)
  rw [← affineModelIso_fst e, ← affineModelIso_snd e, Category.assoc, Category.assoc,
    pullback.condition]

end AffineModels

section PolynomialModels

/-- The affine polynomial algebra with its coefficient-ring structure map. -/
noncomputable def polynomialModel (R A : Type u) [rComm : CommRing R] [aComm : CommRing A]
    [rA : Algebra R A] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (@CommRingCat.ofHom R (Polynomial A)
    rComm (inferInstanceAs (CommRing (Polynomial A))) (algebraMap R (Polynomial A))))

/-- The zero section of the polynomial algebra over its coefficient spectrum. -/
noncomputable def polynomialZero (R A : Type u) [rComm : CommRing R]
    [aComm : CommRing A] [rA : Algebra R A] :
    ((algSpec (.of R)).obj (Opposite.op (CommAlgCat.of R A))) ⟶
      (@polynomialModel.{u} R A rComm aComm rA) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))) (by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial A))) =
        Spec.map (CommRingCat.ofHom (algebraMap R A))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp)

/-- A polynomial algebra of finite presentation has an affine compact,
quasi-separated spectrum whose coefficient map is locally of finite presentation. -/
theorem polynomial_model_properties
    (R A : Type u) [rComm : CommRing R] [aComm : CommRing A]
    [rA : Algebra R A] [Algebra.FinitePresentation R A] :
    CompactSpace (@polynomialModel.{u} R A rComm aComm rA).left ∧
      QuasiSeparatedSpace (@polynomialModel.{u} R A rComm aComm rA).left ∧
      LocallyOfFinitePresentation (@polynomialModel.{u} R A rComm aComm rA).hom := by
  refine ⟨?_, ?_, ?_⟩
  · change CompactSpace (PrimeSpectrum (Polynomial A))
    exact @PrimeSpectrum.compactSpace (Polynomial A)
      (inferInstanceAs (CommSemiring (Polynomial A)))
  · change QuasiSeparatedSpace (Spec (.of (Polynomial A)))
    infer_instance
  · change LocallyOfFinitePresentation (Spec.map (@CommRingCat.ofHom R (Polynomial A)
      rComm (inferInstanceAs (CommRing (Polynomial A))) (algebraMap R (Polynomial A))))
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end PolynomialModels

end FrobeniusSplitting
