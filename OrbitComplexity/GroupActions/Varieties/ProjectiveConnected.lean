import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Geometric integrality of projective space

A nonempty coordinate index makes the zero homogeneous prime a generic point.
The affine charts prove reducedness over a field, and coefficient base change
then proves geometric integrality and geometric connectedness.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GroupActions

private def zeroPoint (K ι : Type u) [Field K] [Nonempty ι] :
    ProjectiveSpectrum (homogeneousSubmodule ι K) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    infer_instance
  not_irrelevant_le := by
    intro h
    let j : ι := Classical.choice inferInstance
    have hx : X j ∈ (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι K)).toIdeal := by
      rw [projective_irrelevant_eq_span]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hz : X j ∈ (⊥ : Ideal (MvPolynomial ι K)) := h hx
    exact X_ne_zero j (Ideal.mem_bot.mp hz)

private theorem projective_irreducible (K ι : Type u) [Field K] [Nonempty ι] :
    IrreducibleSpace (projectiveScheme K ι) := by
  change IrreducibleSpace (ProjectiveSpectrum (homogeneousSubmodule ι K))
  have hc : closure ({zeroPoint K ι} : Set (ProjectiveSpectrum (homogeneousSubmodule ι K))) =
      Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    apply (ProjectiveSpectrum.le_iff_mem_closure _ (zeroPoint K ι) x).mp
    change (⊥ : HomogeneousIdeal (homogeneousSubmodule ι K)) ≤ x.asHomogeneousIdeal
    exact bot_le
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum (homogeneousSubmodule ι K)))
  rw [← hc]
  exact isIrreducible_singleton.closure

/-- Projective space with a finite nonempty coordinate index is integral over a field. -/
instance projectiveScheme_integral (K ι : Type u) [Field K] [Finite ι] [Nonempty ι] :
    IsIntegral (projectiveScheme K ι) := by
  let := projective_irreducible K ι
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Finite projective space with a nonempty coordinate index has integral geometric fibres. -/
instance projectiveToSpec_geometricallyIntegral (R ι : Type u)
    [CommRing R] [Finite ι] [Nonempty ι] : GeometricallyIntegral (projectiveToSpec R ι) := by
  constructor
  intro F hF y Z fst snd h
  let f : R →+* F := (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom f) = y := Spec.map_preimage y
  have h' : IsPullback snd fst (Spec.map (CommRingCat.ofHom f)) (projectiveToSpec R ι) := by
    simpa only [hy] using h.flip
  exact IsIntegral.of_isIso
    ((projectiveBaseChange ι f) ≪≫ h'.isoPullback.symm).hom

/-- Finite projective space with a nonempty coordinate index has connected geometric fibres. -/
instance projectiveToSpec_geometricallyConnected (R ι : Type u)
    [CommRing R] [Finite ι] [Nonempty ι] : GeometricallyConnected (projectiveToSpec R ι) := by
  constructor
  intro F hF y Z fst snd h
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral
    (f := projectiveToSpec R ι) y fst snd h
  infer_instance

end GroupActions
