import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChart
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Function
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussNonvanishing
import Mathlib.RingTheory.PolynomialAlgebra
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The full transverse coefficient polynomial

The original determinant section is pulled back along the translated chart.
Its polynomial in the additive coordinate keeps the entire complementary
root algebra as its coefficient algebra.
-/

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonoidalCategory
open ReductiveGroups TauCeti GroupActions
open scoped TensorProduct

noncomputable section

namespace SchubertGeometry.DeterminantSection

open private SchubertGeometry.DeterminantSection.powerCoordinate from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Morphism
open private SchubertGeometry.DeterminantSection.linePowerCoordinate from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionChart
open private SchubertGeometry.DeterminantSection.spec_app from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Function
open private SchubertGeometry.DeterminantSection.over_appTop_comp
  SchubertGeometry.DeterminantSection.appTop_of_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussNonvanishing

private theorem prefix_chart {C : Type*} [Category C] {T X Y Z : C}
    (e : T ⟶ X) (c : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z)
    (p : Z ⟶ Z) (d : T ⟶ Z) (h : c ≫ q = r ≫ p) (hr : e ≫ r = d) :
    (e ≫ c) ≫ q = d ≫ p := by
  calc
    _ = e ≫ (c ≫ q) := Category.assoc _ _ _
    _ = e ≫ (r ≫ p) := congrArg (e ≫ ·) h
    _ = (e ≫ r) ≫ p := (Category.assoc _ _ _).symm
    _ = d ≫ p := congrArg (· ≫ p) hr

private theorem pullback_composite {S : Scheme} {X Y Z : Over S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : X ⟶ Z)
    (z : Γ(Z.left, ⊤)) (F : Γ(Y.left, ⊤))
    (h : f ≫ q = g) (hq : q.left.appTop z = F) :
    f.left.appTop F = g.left.appTop z := by
  calc
    _ = f.left.appTop (q.left.appTop z) := congrArg f.left.appTop hq.symm
    _ = (f ≫ q).left.appTop z :=
      (SchubertGeometry.DeterminantSection.over_appTop_comp f q z).symm
    _ = g.left.appTop z := SchubertGeometry.DeterminantSection.appTop_of_eq h z

universe u
variable {K : Type u} [Field K]

private def lineSection : Γ((additiveVariety K).scheme, ⊤) :=
  (Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv (SymmetricAlgebra.ι K K 1)

private theorem coordinate_pullback {A : Type u} [CommRing A] [Algebra K A]
    (f : SymmetricAlgebra K K →ₐ[K] A) (q : A)
    (hf : f (SymmetricAlgebra.ι K K 1) = q) :
    (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop (lineSection (K := K)) =
      (Scheme.ΓSpecIso (.of A)).inv q :=
  (SchubertGeometry.DeterminantSection.spec_app f.toRingHom (SymmetricAlgebra.ι K K 1)).trans
    (congrArg (Scheme.ΓSpecIso (.of A)).inv hf)

private theorem affine_section {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] (f : A →ₐ[K] B) (q : A) :
    (affineMorphism f).left.appTop ((Scheme.ΓSpecIso (.of A)).inv q) =
      (Scheme.ΓSpecIso (.of B)).inv (f q) :=
  SchubertGeometry.DeterminantSection.spec_app f.toRingHom q

private theorem power_section (a : Kˣ) (N : ℕ) :
    (oppositionPowerMap a N).left.appTop (lineSection (K := K)) =
      (Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv
        (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
          (SymmetricAlgebra.ι K K 1) ^ (2 * N)) := by
  exact coordinate_pullback (SchubertGeometry.DeterminantSection.linePowerCoordinate a N) _ (by
    simp only [SchubertGeometry.DeterminantSection.linePowerCoordinate,
      SymmetricAlgebra.lift_ι_apply,
      LinearMap.toSpanSingleton_apply, one_smul])

private def tensorPolynomial (A : Type u) [CommRing A] [Algebra K A] :
    A ⊗[K] SymmetricAlgebra K K ≃ₐ[K] Polynomial A :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A)
    (gaPolynomialEquiv K)).trans (polyEquivTensor K A).symm

private theorem tensorPolynomial_right (A : Type u) [CommRing A] [Algebra K A]
    (a : K) (n : ℕ) :
    tensorPolynomial A
      (Algebra.TensorProduct.includeRight
        (algebraMap K (SymmetricAlgebra K K) a * (SymmetricAlgebra.ι K K 1) ^ n)) =
      Polynomial.C (algebraMap K A a) * Polynomial.X ^ n := by
  let p : SymmetricAlgebra K K →ₐ[K] Polynomial A :=
    (tensorPolynomial A).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hgen : p (SymmetricAlgebra.ι K K 1) = Polynomial.X := by
    simp [p, tensorPolynomial, polyEquivTensor_symm_apply_tmul_eq_smul,
      gaPolynomialEquiv_generator]
  change p (algebraMap K (SymmetricAlgebra K K) a * (SymmetricAlgebra.ι K K 1) ^ n) = _
  rw [map_mul, p.commutes a, map_pow, hgen]
  rfl

variable [IsAlgClosed K]

private theorem tensor_domain (A : Type u) [CommRing A] [Algebra K A]
    [IsDomain A] [Algebra.FiniteType K A] :
    IsDomain (A ⊗[K] SymmetricAlgebra K K) := isDomain_tensorProduct

omit [IsAlgClosed K] in
private theorem tensor_finite (A : Type u) [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    Algebra.FiniteType K (A ⊗[K] SymmetricAlgebra K K) :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K A)
    (inferInstance : Algebra.FiniteType A (A ⊗[K] SymmetricAlgebra K K))

attribute [local instance] tensor_domain tensor_finite

variable [CharZero K] (G : ReductiveGroupData K)

private abbrev chartAlgebra (i : G.rootBase.support) :=
  G.rootSubsetAlgebra
    {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i)}
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i))

private def tensorChart (i : G.rootBase.support) :
    (affineVariety K (chartAlgebra G i ⊗[K] SymmetricAlgebra K K)).toOver ⟶
      (reductiveVariety G).toOver :=
  (affineTensorIso K (chartAlgebra G i) (SymmetricAlgebra K K)).hom ≫ oppositionChartMap G i

private theorem determinant_section (N : ℕ) :
    (positiveDetPowerMorphism G N).left.appTop (lineSection (K := K)) =
      positiveDetPowerFunction G N := by
  exact coordinate_pullback (SchubertGeometry.DeterminantSection.powerCoordinate G N)
    (positiveDetPower G N) (by
    simp only [SchubertGeometry.DeterminantSection.powerCoordinate, SymmetricAlgebra.lift_ι_apply,
      LinearMap.toSpanSingleton_apply, one_smul])

/-- The polynomial of the original regular coefficient in the transverse coordinate,
with the whole complementary root algebra as coefficient algebra. -/
def oppositionChartPolynomial (i : G.rootBase.support) (N : ℕ) :
    Polynomial (G.rootSubsetAlgebra
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))) :=
  tensorPolynomial (chartAlgebra G i)
    ((Scheme.ΓSpecIso (.of (chartAlgebra G i ⊗[K] SymmetricAlgebra K K))).hom
      ((tensorChart G i).left.appTop (positiveDetPowerFunction G N)))

private theorem tensorChart_coefficient (i : G.rootBase.support)
    (a : Kˣ) (N : ℕ)
    (h : oppositionChartMap G i ≫ positiveDetPowerMorphism G N =
      snd _ _ ≫ oppositionPowerMap a N) :
    (tensorChart G i).left.appTop (positiveDetPowerFunction G N) =
      (Scheme.ΓSpecIso (.of (chartAlgebra G i ⊗[K] SymmetricAlgebra K K))).inv
        (Algebra.TensorProduct.includeRight
          (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
            (SymmetricAlgebra.ι K K 1) ^ (2 * N))) := by
  let d : (affineVariety K (chartAlgebra G i ⊗[K] SymmetricAlgebra K K)).toOver ⟶
      (additiveVariety K).toOver :=
    affineMorphism (Algebra.TensorProduct.includeRight :
      SymmetricAlgebra K K →ₐ[K] chartAlgebra G i ⊗[K] SymmetricAlgebra K K)
  have hmap : tensorChart G i ≫ positiveDetPowerMorphism G N = d ≫ oppositionPowerMap a N :=
    prefix_chart (affineTensorIso K (chartAlgebra G i) (SymmetricAlgebra K K)).hom
      (oppositionChartMap G i) (positiveDetPowerMorphism G N) (snd _ _)
      (oppositionPowerMap a N) d h
      (affineTensorIso_snd K (chartAlgebra G i) (SymmetricAlgebra K K))
  have hspec : d.left.appTop
      ((Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv
        (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
          (SymmetricAlgebra.ι K K 1) ^ (2 * N))) =
      (Scheme.ΓSpecIso (.of (chartAlgebra G i ⊗[K] SymmetricAlgebra K K))).inv
        ((Algebra.TensorProduct.includeRight :
          SymmetricAlgebra K K →ₐ[K] chartAlgebra G i ⊗[K] SymmetricAlgebra K K)
          (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
            (SymmetricAlgebra.ι K K 1) ^ (2 * N))) :=
    affine_section
      (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra K K →ₐ[K] chartAlgebra G i ⊗[K] SymmetricAlgebra K K)
      (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
        (SymmetricAlgebra.ι K K 1) ^ (2 * N))
  have hfirst := pullback_composite (tensorChart G i) (positiveDetPowerMorphism G N)
    (d ≫ oppositionPowerMap a N) (lineSection (K := K))
    (positiveDetPowerFunction G N) hmap (determinant_section G N)
  have hsecond := SchubertGeometry.DeterminantSection.over_appTop_comp d
    (oppositionPowerMap a N) (lineSection (K := K))
  have hthird := congrArg d.left.appTop (power_section a N)
  exact hfirst.trans (hsecond.trans (hthird.trans hspec))

/-- The transverse polynomial has one constant torus scalar in every degree. -/
theorem oppositionChartPolynomial_formula (i : G.rootBase.support) :
    ∃ a : Kˣ, ∀ N : ℕ,
      oppositionChartPolynomial G i N =
        Polynomial.C (algebraMap K (chartAlgebra G i) ((a : K) ^ N)) * Polynomial.X ^ (2 * N) := by
  obtain ⟨a, ha⟩ := oppositionChartMap_coefficient G i
  refine ⟨a, fun N => ?_⟩
  have hsection := tensorChart_coefficient G i a N (ha N)
  have hinv := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (.of (chartAlgebra G i ⊗[K] SymmetricAlgebra K K))).inv_hom_id
    (Algebra.TensorProduct.includeRight
      (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
        (SymmetricAlgebra.ι K K 1) ^ (2 * N)))
  change tensorPolynomial (chartAlgebra G i)
      ((Scheme.ΓSpecIso (.of (chartAlgebra G i ⊗[K] SymmetricAlgebra K K))).hom
        ((tensorChart G i).left.appTop (positiveDetPowerFunction G N))) = _
  exact (congrArg (fun q => tensorPolynomial (chartAlgebra G i)
    ((Scheme.ΓSpecIso (.of (chartAlgebra G i ⊗[K] SymmetricAlgebra K K))).hom q)) hsection).trans
      ((congrArg (tensorPolynomial (chartAlgebra G i)) hinv).trans
        (tensorPolynomial_right (chartAlgebra G i) ((a : K) ^ N) (2 * N)))

private theorem unit_map_value {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (a : Rˣ) : (Units.map f.toMonoidHom a : A) = f (a : R) := rfl

/-- The unpowered transverse polynomial is a unit times X squared in the full
complementary coefficient algebra. -/
theorem oppositionChartPolynomial_square (i : G.rootBase.support) :
    ∃ a : (chartAlgebra G i)ˣ,
      oppositionChartPolynomial G i 1 = Polynomial.C (a : chartAlgebra G i) * Polynomial.X ^ 2 := by
  obtain ⟨a, ha⟩ := oppositionChartPolynomial_formula G i
  refine ⟨Units.map (algebraMap K (chartAlgebra G i)).toMonoidHom a, ?_⟩
  have h1 : oppositionChartPolynomial G i 1 =
      Polynomial.C (algebraMap K (chartAlgebra G i) (a : K)) * Polynomial.X ^ 2 := by
    simpa only [pow_one, mul_one] using ha 1
  exact h1.trans (congrArg (fun q : chartAlgebra G i => Polynomial.C q * Polynomial.X ^ 2)
    (unit_map_value (algebraMap K (chartAlgebra G i)) a).symm)

end SchubertGeometry.DeterminantSection
