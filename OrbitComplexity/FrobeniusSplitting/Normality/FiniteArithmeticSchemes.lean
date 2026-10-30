import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ArithmeticSchemes
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeFiniteness

/-!
# Finite-presentation arithmetic scheme models
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- A quasi-compact scheme with affine diagonal admits a Noetherian coefficient model
whose structure map is of finite presentation. -/
theorem exists_finite_arithmetic_scheme {X : Scheme.{u}} {K : Type u} [CommRing K]
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    ∃ (R : Subalgebra ℤ K) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of R)) (q : X ⟶ X₀),
      R.FG ∧ AlgebraicGeometry.IsNoetherian X₀ ∧ LocallyOfFinitePresentation f₀ ∧
      QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
      IsPullback q f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨R, X₀, f₀, q, hfg, hcompact, hfp, hcart⟩ := exists_arithmetic_scheme f
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hfg
  have : CompactSpace X₀ := hcompact
  have : LocallyOfFinitePresentation f₀ := hfp
  obtain ⟨hnoeth, hqc, hqs⟩ := finiteType_int_scheme_properties f₀
  exact ⟨R, X₀, f₀, q, hfg, hnoeth, hfp, hqc, hqs, hcart⟩

end FrobeniusSplitting
