import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# AffineGenerators
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

private abbrev affineCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

/-- Global coordinates of an affine scheme locally of finite type admit a
finite algebra-generating tuple over the base ring. -/
theorem exists_affine_generators (K : Type u) [CommRing K] (Y : Scheme.{u})
    [Y.Over (Spec (.of K))] [IsAffine Y] [LocallyOfFiniteType (Y ↘ Spec (.of K))] :
    letI : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
    ∃ m : ℕ, ∃ c : Fin m → Γ(Y, ⊤), Algebra.adjoin K (Set.range c) = ⊤ := by
  let : Algebra K Γ(Y, ⊤) := affineCoordinateAlgebra (.of K) Y
  have he : Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, ⊤))) =
      Y.isoSpec.inv ≫ (Y ↘ Spec (.of K)) := by
    have hmap := algebraMap_presheafObj (R := CommRingCat.of K) (X := Y)
    change algebraMap K Γ(Y, ⊤) = _ at hmap
    rw [hmap]
    exact Spec.fullyFaithful.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, ⊤)))) := by
    rw [he]
    infer_instance
  have : Algebra.FiniteType K Γ(Y, ⊤) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap K Γ(Y, ⊤)))).mp hft
  obtain ⟨m, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := K) (S := Γ(Y, ⊤))).mp inferInstance
  let c : Fin m → Γ(Y, ⊤) := fun i ↦ f (MvPolynomial.X i)
  refine ⟨m, c, ?_⟩
  have h : MvPolynomial.aeval c = f := by
    ext i
    simp only [MvPolynomial.aeval_X, c]
  rw [Algebra.adjoin_range_eq_range_aeval, h]
  exact (AlgHom.range_eq_top f).mpr hf

end

end GroupActions
