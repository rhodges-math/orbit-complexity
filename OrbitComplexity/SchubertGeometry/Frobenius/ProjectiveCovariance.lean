import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorSums
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveOperators
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Projective Cartier covariance over affine coefficient rings -/

namespace FrobeniusSplitting.SchemeFrobeniusMap
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} {p : ℕ}

/-- A transported chart formula commutes with pulling back sections to that chart. -/
private theorem naturality_of_restrict (φ : SchemeFrobeniusMap X p) (U : X.Opens)
    (e : S ≅ U.toScheme) (σ : SchemeFrobeniusMap S p)
    (h : φ.restrict U = σ.pushforward e.hom) (V : X.Opens) (s : Γ(X, V)) :
    σ.onOpen ((e.hom ≫ U.ι) ⁻¹ᵁ V) ((e.hom ≫ U.ι).app V s) =
      (e.hom ≫ U.ι).app V (φ.onOpen V s) := by
  change σ.onOpen (e.hom ⁻¹ᵁ U.ι ⁻¹ᵁ V)
      (e.hom.app (U.ι ⁻¹ᵁ V) (U.ι.app V s)) =
    e.hom.app (U.ι ⁻¹ᵁ V) (U.ι.app V (φ.onOpen V s))
  rw [← pushforward_app, ← h]
  exact congrArg (e.hom.app (U.ι ⁻¹ᵁ V))
    (φ.restrict_comm (Set.image_preimage_subset _ _) s)

/-- Naturality on a scheme follows from a commuting scheme-theoretically dense chart. -/
private theorem naturality_of_dense_chart (i : S ⟶ X)
    [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (f : X ⟶ X) (a : S ⟶ S) (he : a ≫ i = i ≫ f)
    (φ ψ : SchemeFrobeniusMap X p) (σ τ : SchemeFrobeniusMap S p)
    (hφ : ∀ (V : X.Opens) (s : Γ(X, V)),
      σ.onOpen (i ⁻¹ᵁ V) (i.app V s) = i.app V (φ.onOpen V s))
    (hψ : ∀ (V : X.Opens) (s : Γ(X, V)),
      τ.onOpen (i ⁻¹ᵁ V) (i.app V s) = i.app V (ψ.onOpen V s))
    (ha : ∀ (V : S.Opens) (s : Γ(S, V)),
      σ.onOpen (a ⁻¹ᵁ V) (a.app V s) = a.app V (τ.onOpen V s))
    (V : X.Opens) (s : Γ(X, V)) :
    φ.onOpen (f ⁻¹ᵁ V) (f.app V s) = f.app V (ψ.onOpen V s) := by
  have hcomposite (W : X.Opens) (t : Γ(X, W)) :
      σ.onOpen ((i ≫ f) ⁻¹ᵁ W) ((i ≫ f).app W t) =
        (i ≫ f).app W (ψ.onOpen W t) := by
    rw [← he]
    change σ.onOpen (a ⁻¹ᵁ i ⁻¹ᵁ W) (a.app (i ⁻¹ᵁ W) (i.app W t)) =
      a.app (i ⁻¹ᵁ W) (i.app W (ψ.onOpen W t))
    rw [ha, hψ]
  apply i.app_injective (f ⁻¹ᵁ V)
  rw [← hφ]
  exact hcomposite V s

end FrobeniusSplitting.SchemeFrobeniusMap

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory Opposite GroupActions
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem spec_dominant {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) := by
  have hi : Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).injective
    apply hf
    change ((Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom f) a =
      ((Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom f) b
    rw [← Scheme.ΓSpecIso_naturality]
    exact congrArg (Scheme.ΓSpecIso (.of S)).hom hab
  have hz : RingHom.ker (Spec.map (CommRingCat.ofHom f)).appTop.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hi
  constructor
  rw [Scheme.ker_of_isAffine, hz]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp

private abbrev chartIndex : Type u := ULift.{u} (Fin 2)

/-- The first standard chart is schematically dense even over a nonreduced coefficient ring. -/
private theorem projectiveChart_schematicallyDominant (R : Type u) [CommRing R] :
    IsSchemeTheoreticallyDominant
      (projectiveLinePolynomialChart R (⟨0⟩ : ULift.{u} (Fin 2))) := by
  let f := projectiveLinePolynomialChart R (⟨0⟩ : chartIndex.{u})
  let g := projectiveLinePolynomialChart R (⟨1⟩ : chartIndex.{u})
  let a : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
    Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  let b : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
    Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom.comp
        Polynomial.toLaurent))
  let : IsSchemeTheoreticallyDominant b := spec_dominant _
    ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).injective.comp
      Polynomial.toLaurent_injective)
  have hab : a ≫ f = b ≫ g := projectiveLinePolynomial_overlap R
  have hk : f.ker ≤ g.ker := by
    calc
      f.ker ≤ (a ≫ f).ker := a.le_ker_comp f
      _ = (b ≫ g).ker := congrArg Scheme.Hom.ker hab
      _ = g.ker := by
        rw [Scheme.Hom.ker_comp, b.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  let U : chartIndex.{u} → (projectiveScheme R chartIndex.{u}).affineOpens := fun j =>
    ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule chartIndex.{u} R) (MvPolynomial.X j),
      Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one⟩
  have hcover : (⨆ j, (U j).1) = ⊤ :=
    Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule chartIndex.{u} R)
      (MvPolynomial.X : chartIndex.{u} → MvPolynomial chartIndex.{u} R)
        (projective_irrelevant_eq_span R chartIndex.{u}).le
  constructor
  apply le_antisymm _ bot_le
  apply Scheme.IdealSheafData.le_of_iSup_eq_top U hcover
  intro j
  have hj : f.ker ≤ (projectiveLinePolynomialChart R j).ker := by
    rcases j with ⟨j⟩
    fin_cases j
    · exact le_rfl
    · exact hk
  have : IsIso ((projectiveLinePolynomialChart R j).app (U j)) :=
    (projectiveLinePolynomialChart R j).isIso_app _ (by
      rw [projectiveLinePolynomialChart_range])
  have hz : RingHom.ker ((projectiveLinePolynomialChart R j).app (U j)).hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot ((projectiveLinePolynomialChart R j).app (U j)).hom).mp
      (ConcreteCategory.bijective_of_isIso
        ((projectiveLinePolynomialChart R j).app (U j))).injective
  simpa only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, hz] using
    (hj (U j)).trans ((projectiveLinePolynomialChart R j).ideal_ker_le (U j))

end
end SchubertGeometry

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory GroupActions FrobeniusSplitting Polynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {p : ℕ} [ExpChar R p]

private abbrev lineIndex : Type u := ULift.{u} (Fin 2)

private def coefficient (a : R) : Γ(projectiveScheme R lineIndex.{u}, ⊤) :=
  (projectiveToSpec R lineIndex.{u}).appTop ((Scheme.ΓSpecIso (.of R)).inv a)

private def projectiveLineTranslationOperator (base : RingSplitting R p) (a : R) :
    SchemeFrobeniusMap (projectiveScheme R (ULift.{u} (Fin 2))) p :=
  SchemeFrobeniusMap.inputSum (projectiveLineCanonicalOperator base)
    (fun j : Fin p => coefficient (a ^ (j : ℕ)))

private def chartWeight (base : RingSplitting R p) (j : Fin p) :
    FrobeniusLinearMap (Polynomial R) p :=
  (univariateTrace base).weight
    (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 - j))

private theorem ring_combination (base : RingSplitting R p) (a : R) :
    base.univariate.toOperator.transport (Polynomial.algEquivAevalXAddC a).toRingEquiv =
      FrobeniusLinearMap.inputSum (chartWeight base) (fun j : Fin p => C (a ^ (j : ℕ))) := by
  apply FrobeniusLinearMap.ext
  intro f
  change (base.univariate (f.comp (X - C a))).comp (X + C a) =
    ∑ j : Fin p, (chartWeight base j) (C (a ^ (j : ℕ)) * f)
  let F : ℕ → Polynomial R := fun j =>
    ((univariateTrace base).weight
      (C ((Nat.choose (p - 1) j : ℕ) : R) * X ^ (p - 1 - j))) (C (a ^ j) * f)
  have hsum : (∑ j : Fin p, F j) = ∑ j ∈ Finset.range p, F j :=
    Fin.sum_univ_eq_sum_range F p
  exact (univariate_conj_translate_sum base a f).trans hsum.symm

private theorem coefficient_chart (a : R) :
    (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).appTop (coefficient a) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (C a) := by
  change (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) ≫
      projectiveToSpec R lineIndex.{u}).appTop ((Scheme.ΓSpecIso (.of R)).inv a) = _
  rw [projectiveLinePolynomialChart_base]
  exact (congrArg (fun g : CommRingCat.of R ⟶ Γ(Spec (.of (Polynomial R)), ⊤) => g a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (C : R →+* Polynomial R)))).symm

private theorem family_chart_natural (base : RingSplitting R p) (j : Fin p)
    (V : (projectiveScheme R lineIndex.{u}).Opens)
    (s : Γ(projectiveScheme R lineIndex.{u}, V)) :
    ((chartWeight base j).toSpec (expChar_pos R p)).onOpen
        (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) ⁻¹ᵁ V)
        ((projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).app V s) =
      (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).app V
        ((projectiveLineCanonicalOperator base j).onOpen V s) := by
  apply SchemeFrobeniusMap.naturality_of_restrict _ _
    (projectiveLinePolynomialIso R (⟨0⟩ : lineIndex.{u}))
  simpa only [chartWeight, ↓reduceIte] using
    projectiveLineCanonicalOperator_chart base j (⟨0⟩ : lineIndex.{u})

private theorem combination_chart_natural (base : RingSplitting R p) (a : R)
    (V : (projectiveScheme R lineIndex.{u}).Opens)
    (s : Γ(projectiveScheme R lineIndex.{u}, V)) :
    ((FrobeniusLinearMap.inputSum (chartWeight base)
        (fun j : Fin p => C (a ^ (j : ℕ)))).toSpec (expChar_pos R p)).onOpen
        (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) ⁻¹ᵁ V)
        ((projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).app V s) =
      (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).app V
        ((projectiveLineTranslationOperator base a).onOpen V s) := by
  rw [FrobeniusLinearMap.inputSum_toSpec]
  apply SchemeFrobeniusMap.inputSum_naturality
  · intro j
    exact coefficient_chart (a ^ (j : ℕ))
  · exact family_chart_natural base

private theorem family_standard_trace {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]
    (base : RingSplitting R p) :
    (univariateTrace base).weight (X ^ (p - 1)) = base.univariate.toOperator := by
  apply FrobeniusLinearMap.ext
  intro f
  apply Polynomial.ext
  intro n
  change (univariateTrace base (X ^ (p - 1) * f)).coeff n = (base.univariate f).coeff n
  rw [univariateTrace_coeff, coeff_X_pow_mul, RingSplitting.univariate_coeff]

private theorem splitting_chart_natural (base : RingSplitting R p)
    (V : (projectiveScheme R lineIndex.{u}).Opens)
    (s : Γ(projectiveScheme R lineIndex.{u}, V)) :
    (base.univariate.toOperator.toSpec (expChar_pos R p)).onOpen
        (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u}) ⁻¹ᵁ V)
        ((projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).app V s) =
      (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})).app V
        ((projectiveLineSplitting base).toOperator.onOpen V s) := by
  rw [← projectiveLineCanonicalOperator_zero]
  have h := family_chart_natural base ⟨0, expChar_pos R p⟩ V s
  simpa only [chartWeight, Nat.choose_zero_right, Nat.cast_one, map_one, one_mul,
    Nat.sub_zero, family_standard_trace] using h

private theorem affine_conjugation (base : RingSplitting R p) (a : R)
    (V : (Spec (.of (Polynomial R))).Opens) (s : Γ(Spec (.of (Polynomial R)), V)) :
    (base.univariate.toOperator.toSpec (expChar_pos R p)).onOpen
        (Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC (-a)).toRingHom) ⁻¹ᵁ V)
        ((Spec.map (CommRingCat.ofHom
          (Polynomial.algEquivAevalXAddC (-a)).toRingHom)).app V s) =
      (Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC (-a)).toRingHom)).app V
        (((FrobeniusLinearMap.inputSum (chartWeight base)
          (fun j : Fin p => C (a ^ (j : ℕ)))).toSpec (expChar_pos R p)).onOpen V s) := by
  apply FrobeniusLinearMap.toSpec_naturality
  intro f
  rw [← ring_combination]
  rw [← Polynomial.algEquivAevalXAddC_symm]
  change base.univariate ((Polynomial.algEquivAevalXAddC a).symm f) =
    (Polynomial.algEquivAevalXAddC a).symm
      ((Polynomial.algEquivAevalXAddC a)
        (base.univariate ((Polynomial.algEquivAevalXAddC a).symm f)))
  rw [AlgEquiv.symm_apply_apply]

/-- Geometric translation by the negative parameter conjugates the splitting to its binomial sum. -/
theorem projectiveLineTranslation_conjugation {K : Type u} [CommRing K] {p : ℕ}
    [ExpChar K p] (base : RingSplitting K p) (a : K) :
    (projectiveLineSplitting base).toOperator.pushforward
        (projectiveLineTranslationIso (-a)).hom =
      SchemeFrobeniusMap.inputSum (projectiveLineCanonicalOperator base)
        (fun j : Fin p => (projectiveToSpec _ (ULift.{u} (Fin 2))).appTop
          ((Scheme.ΓSpecIso _).inv (a ^ (j : ℕ)))) := by
  let := projectiveChart_schematicallyDominant K
  let : QuasiCompact (projectiveLinePolynomialChart K (⟨0⟩ : lineIndex.{u})) :=
    inferInstance
  apply SchemeFrobeniusMap.ext
  intro V s
  apply (asIso ((projectiveLineTranslationIso (-a)).hom.app V)).commRingCatIsoToRingEquiv.injective
  change (projectiveLineTranslationIso (-a)).hom.app V
      (((projectiveLineSplitting base).toOperator.pushforward
        (projectiveLineTranslationIso (-a)).hom).onOpen V s) =
    (projectiveLineTranslationIso (-a)).hom.app V
      ((projectiveLineTranslationOperator base a).onOpen V s)
  rw [SchemeFrobeniusMap.pushforward_app]
  exact SchemeFrobeniusMap.naturality_of_dense_chart
    (projectiveLinePolynomialChart K (⟨0⟩ : lineIndex.{u}))
    (projectiveLineTranslationIso (-a)).hom
    (Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC (-a)).toRingHom))
    (projectiveLineTranslation_chart (-a))
    (projectiveLineSplitting base).toOperator (projectiveLineTranslationOperator base a)
    (base.univariate.toOperator.toSpec (expChar_pos K p))
    ((FrobeniusLinearMap.inputSum (chartWeight base)
      (fun j : Fin p => C (a ^ (j : ℕ)))).toSpec (expChar_pos K p))
    (splitting_chart_natural base) (combination_chart_natural base a)
    (affine_conjugation base a) V s


private theorem polynomial_scale (base : RingSplitting R p) (c : R) (f : Polynomial R) :
    base.univariate (f.comp (C c * X)) = (base.univariate f).comp (C c * X) := by
  apply Polynomial.ext
  intro n
  rw [RingSplitting.univariate_coeff, comp_C_mul_X_coeff,
    comp_C_mul_X_coeff, RingSplitting.univariate_coeff]
  calc
    base (f.coeff (p * n) * c ^ (p * n)) =
        base ((c ^ n) ^ p * f.coeff (p * n)) := by
      congr 1
      rw [← pow_mul, Nat.mul_comm n p, mul_comm]
    _ = c ^ n * base (f.coeff (p * n)) := base.map_pow_mul _ _
    _ = _ := mul_comm _ _

private theorem affine_scaling (base : RingSplitting R p) (c : Rˣ)
    (V : (Spec (.of (Polynomial R))).Opens) (s : Γ(Spec (.of (Polynomial R)), V)) :
    (base.univariate.toOperator.toSpec (expChar_pos R p)).onOpen
        (Spec.map (CommRingCat.ofHom
          (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom) ⁻¹ᵁ V)
        ((Spec.map (CommRingCat.ofHom
          (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom)).app V s) =
      (Spec.map (CommRingCat.ofHom
        (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom)).app V
        ((base.univariate.toOperator.toSpec (expChar_pos R p)).onOpen V s) := by
  apply FrobeniusLinearMap.toSpec_naturality
  intro f
  change base.univariate (Polynomial.algEquivCMulXAddC (c : R) 0 f) =
    Polynomial.algEquivCMulXAddC (c : R) 0 (base.univariate f)
  simpa only [Polynomial.algEquivCMulXAddC_apply, map_zero, add_zero, ← comp_eq_aeval] using
    polynomial_scale base (c : R) f

/-- Scaling by a unit of the coefficient ring preserves the projective-line splitting. -/
theorem projectiveLineScaling_conjugation (base : RingSplitting R p) (c : Rˣ) :
    (projectiveLineSplitting base).toOperator.pushforward (projectiveLineScalingIso c).hom =
      (projectiveLineSplitting base).toOperator := by
  let := projectiveChart_schematicallyDominant R
  let : QuasiCompact (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})) := inferInstance
  apply SchemeFrobeniusMap.ext
  intro V s
  apply (asIso ((projectiveLineScalingIso c).hom.app V)).commRingCatIsoToRingEquiv.injective
  change (projectiveLineScalingIso c).hom.app V
      (((projectiveLineSplitting base).toOperator.pushforward
        (projectiveLineScalingIso c).hom).onOpen V s) =
    (projectiveLineScalingIso c).hom.app V ((projectiveLineSplitting base).toOperator.onOpen V s)
  rw [SchemeFrobeniusMap.pushforward_app]
  exact SchemeFrobeniusMap.naturality_of_dense_chart
    (projectiveLinePolynomialChart R (⟨0⟩ : lineIndex.{u})) (projectiveLineScalingIso c).hom
    (Spec.map (CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom))
    (projectiveLineScaling_chart c)
    (projectiveLineSplitting base).toOperator (projectiveLineSplitting base).toOperator
    (base.univariate.toOperator.toSpec (expChar_pos R p))
    (base.univariate.toOperator.toSpec (expChar_pos R p))
    (splitting_chart_natural base) (splitting_chart_natural base) (affine_scaling base c) V s


private theorem pushforward_comp {X Y Z : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] :
    φ.pushforward (f ≫ g) = (φ.pushforward f).pushforward g := by
  apply SchemeFrobeniusMap.ext
  intro U s
  apply (asIso ((f ≫ g).app U)).commRingCatIsoToRingEquiv.injective
  change (f ≫ g).app U ((φ.pushforward (f ≫ g)).onOpen U s) =
    (f ≫ g).app U (((φ.pushforward f).pushforward g).onOpen U s)
  rw [SchemeFrobeniusMap.pushforward_app]
  change φ.onOpen (f ⁻¹ᵁ g ⁻¹ᵁ U) (f.app (g ⁻¹ᵁ U) (g.app U s)) =
    f.app (g ⁻¹ᵁ U) (g.app U (((φ.pushforward f).pushforward g).onOpen U s))
  rw [SchemeFrobeniusMap.pushforward_app, SchemeFrobeniusMap.pushforward_app]

/-- The affine-coordinate family has the binomial input-weighted covariance formula. -/
theorem projectiveLineAffine_conjugation {R : Type u} [CommRing R] {p : ℕ} [ExpChar R p]
    (base : RingSplitting R p) (c : Rˣ) (a : R) :
    (projectiveLineSplitting base).toOperator.pushforward
        ((projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom) =
      SchemeFrobeniusMap.inputSum (projectiveLineCanonicalOperator base)
        (fun j : Fin p => (projectiveToSpec _ (ULift.{u} (Fin 2))).appTop
          ((Scheme.ΓSpecIso _).inv ((-a) ^ (j : ℕ)))) := by
  rw [pushforward_comp, projectiveLineScaling_conjugation]
  simpa only [neg_neg] using projectiveLineTranslation_conjugation base (-a)

end
end SchubertGeometry
