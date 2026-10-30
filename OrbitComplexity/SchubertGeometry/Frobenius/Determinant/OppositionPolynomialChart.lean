import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionBoundary
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Polynomial coordinates on the transverse flag chart

The polynomial coordinate chart preserves the original determinant section.
Its evaluation at zero is the zero section of the complementary root chart.
-/

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonoidalCategory
open ReductiveGroups TauCeti GroupActions WithConv
open scoped TensorProduct

noncomputable section

namespace SchubertGeometry.DeterminantSection

open private SchubertGeometry.DeterminantSection.tensorPolynomial
  SchubertGeometry.DeterminantSection.tensorPolynomial_right
  SchubertGeometry.DeterminantSection.tensor_domain
  SchubertGeometry.DeterminantSection.tensor_finite
  SchubertGeometry.DeterminantSection.chartAlgebra
  SchubertGeometry.DeterminantSection.tensorChart
  SchubertGeometry.DeterminantSection.affine_section from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private SchubertGeometry.DeterminantSection.over_appTop_comp
  SchubertGeometry.DeterminantSection.appTop_of_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussNonvanishing

attribute [local instance] SchubertGeometry.DeterminantSection.tensor_domain
  SchubertGeometry.DeterminantSection.tensor_finite

private theorem compose_iso_zero {C : Type*} [Category C] {X Y Z W V : C}
    (u : X ⟶ Y) (e : Y ≅ Z) (f : Z ≅ W) (g : W ≅ V) (z : X ⟶ W)
    (h : (u ≫ e.hom) ≫ f.hom = z) :
    u ≫ (e ≪≫ f ≪≫ g).hom = z ≫ g.hom := by
  calc
    _ = ((u ≫ e.hom) ≫ f.hom) ≫ g.hom := by
      simp only [Iso.trans_hom, Category.assoc]
    _ = _ := congrArg (· ≫ g.hom) h

private theorem iso_chart_comp {C : Type*} [Category C] {X Y Z W V : C}
    (e : X ≅ Y) (f : Y ≅ Z) (g : Z ≅ W) (q : W ⟶ V) :
    (e ≪≫ f ≪≫ g).hom ≫ q = e.hom ≫ (f.hom ≫ (g.hom ≫ q)) := by
  simp only [Iso.trans_hom, Category.assoc]

private theorem zero_left_transport {S : Scheme} {X Y Z : Over S}
    (f : X ⟶ Y) (e : Y ≅ Z) (g : X ⟶ Z) (u : X.left ⟶ Y.left)
    (hf : f.left = u) (h : f ≫ e.hom = g) : u ≫ e.hom.left = g.left := by
  calc
    _ = f.left ≫ e.hom.left := congrArg (· ≫ e.hom.left) hf.symm
    _ = (f ≫ e.hom).left := rfl
    _ = g.left := congrArg Over.Hom.left h

universe u
variable {K : Type u} [Field K]

/-- An affine coordinate as a global section of its variety. -/
def affineSection (A : Type u) [CommRing A] [Algebra K A]
    [IsReduced A] [Algebra.FiniteType K A] :
    A →+* Γ((affineVariety K A).toOver.left, ⊤) :=
  (Scheme.ΓSpecIso (.of A)).inv.hom

private def evalZero (A : Type u) [CommRing A] [Algebra K A] : Polynomial A →ₐ[K] A :=
  (Polynomial.aeval (0 : A)).restrictScalars K

private theorem evalZero_ring (A : Type u) [CommRing A] [Algebra K A] :
    (evalZero (K := K) A).toRingHom = Polynomial.evalRingHom (0 : A) := by
  ext a <;> simp [evalZero]

private theorem tensor_left (A : Type u) [CommRing A] [Algebra K A] (a : A) :
    SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A
      ((Algebra.TensorProduct.includeLeft : A →ₐ[K]
        A ⊗[K] SymmetricAlgebra K K) a) = Polynomial.C a := by
  simp [SchubertGeometry.DeterminantSection.tensorPolynomial,
    polyEquivTensor_symm_apply_tmul_eq_smul, Algebra.smul_def]

private theorem tensor_generator (A : Type u) [CommRing A] [Algebra K A] :
    SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A
      (Algebra.TensorProduct.includeRight (SymmetricAlgebra.ι K K 1)) = Polynomial.X := by
  simpa only [map_one, one_mul, pow_one, Polynomial.C_1] using
    SchubertGeometry.DeterminantSection.tensorPolynomial_right (K := K) A (1 : K) 1

private theorem zero_left (A : Type u) [CommRing A] [Algebra K A] :
    ((evalZero (K := K) A).comp
      (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A).toAlgHom).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] SymmetricAlgebra K K) =
        AlgHom.id K A := by
  ext a
  change evalZero (K := K) A (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A
    ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] SymmetricAlgebra K K) a)) = a
  rw [tensor_left (K := K)]
  simp [evalZero]

private theorem zero_generator (A : Type u) [CommRing A] [Algebra K A] :
    (((evalZero (K := K) A).comp
      (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A).toAlgHom).comp
      (Algebra.TensorProduct.includeRight : SymmetricAlgebra K K →ₐ[K]
        A ⊗[K] SymmetricAlgebra K K)) (SymmetricAlgebra.ι K K 1) = 0 := by
  change evalZero (K := K) A (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A
    (Algebra.TensorProduct.includeRight (SymmetricAlgebra.ι K K 1))) = 0
  rw [tensor_generator (K := K)]
  simp [evalZero]

private def algebraIso {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] (e : A ≃ₐ[K] B) :
    (affineVariety K B).toOver ≅ (affineVariety K A).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk e).op

private theorem algebraIso_hom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] (e : A ≃ₐ[K] B) :
    (algebraIso e).hom = affineMorphism e.toAlgHom := rfl

private theorem affine_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C] [IsReduced A] [IsReduced B] [IsReduced C]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] [Algebra.FiniteType K C]
    (f : A →ₐ[K] B) (g : C →ₐ[K] A) :
    affineMorphism f ≫ affineMorphism g = affineMorphism (f.comp g) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom g.toRingHom) =
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem affine_id (A : Type u) [CommRing A] [Algebra K A]
    [IsReduced A] [Algebra.FiniteType K A] : affineMorphism (AlgHom.id K A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id (.of A)

private theorem evalZero_spec (A : Type u) [CommRing A] [Algebra K A]
    [IsDomain A] [Algebra.FiniteType K A] :
    (affineMorphism (evalZero (K := K) A)).left =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) :=
  congrArg (fun f : Polynomial A →+* A => Spec.map (CommRingCat.ofHom f))
    (evalZero_ring (K := K) A)

private theorem affine_point_compare {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (f : A →ₐ[K] B) (p : B →ₐ[K] K) (q : A →ₐ[K] K)
    (y : (affineVariety K A).points)
    (hy : (affineVarietyPointsEquiv K A).symm q = y) (h : p.comp f = q) :
    Variety.mapPoints (affineMorphism f) ((affineVarietyPointsEquiv K B).symm p) = y :=
  (affineMorphism_points f p).trans
    ((congrArg (affineVarietyPointsEquiv K A).symm h).trans hy)

private theorem constant_zero_points (X : Variety K) (x : X.points) :
    Variety.mapPoints (toUnit X.toOver ≫
      (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) x =
      additivePointsEquiv K 0 := by
  apply (additiveVariety K).pointsEquivOverHom.injective
  change X.pointsEquivOverHom x ≫ (toUnit X.toOver ≫
    (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) = _
  rw [← Category.assoc]
  have h : X.pointsEquivOverHom x ≫ toUnit X.toOver = 𝟙 _ := Subsingleton.elim _ _
  rw [h, Category.id_comp]

private theorem coordinate_points {A : Type u} [CommRing A] [Algebra K A]
    [IsReduced A] [Algebra.FiniteType K A] (f : SymmetricAlgebra K K →ₐ[K] A)
    (p : A →ₐ[K] K) (t : K) (ht : (p.comp f) (SymmetricAlgebra.ι K K 1) = t) :
    Variety.mapPoints (affineMorphism f) ((affineVarietyPointsEquiv K A).symm p) =
      additivePointsEquiv K t := by
  let q := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have hgen : (p.comp f) (SymmetricAlgebra.ι K K 1) = q (SymmetricAlgebra.ι K K 1) := by
    exact ht.trans (by simp [q, AdditiveGroup.gaPointsMulEquiv_symm_apply_ι])
  have he : p.comp f = q := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro a
    have hι : SymmetricAlgebra.ι K K a = a • SymmetricAlgebra.ι K K 1 := by
      simpa only [smul_eq_mul, mul_one] using (map_smul (SymmetricAlgebra.ι K K) a (1 : K))
    change (p.comp f) (SymmetricAlgebra.ι K K a) = q (SymmetricAlgebra.ι K K a)
    rw [hι, map_smul, map_smul, hgen]
  exact affine_point_compare f p q (additivePointsEquiv K t) rfl he

private theorem algebraIso_section {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] (e : A ≃ₐ[K] B)
    (s : Γ((affineVariety K A).scheme, ⊤)) :
    (algebraIso e).hom.left.appTop s =
      (Scheme.ΓSpecIso (.of B)).inv (e ((Scheme.ΓSpecIso (.of A)).hom s)) := by
  have hs : (Scheme.ΓSpecIso (.of A)).inv ((Scheme.ΓSpecIso (.of A)).hom s) = s :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).hom_inv_id s
  have hfirst := congrArg (algebraIso e).hom.left.appTop hs.symm
  have hsecond := congrArg
    (fun f : (affineVariety K B).toOver ⟶ (affineVariety K A).toOver => f.left.appTop
      ((Scheme.ΓSpecIso (.of A)).inv ((Scheme.ΓSpecIso (.of A)).hom s))) (algebraIso_hom e)
  have hthird := SchubertGeometry.DeterminantSection.affine_section e.toAlgHom
    ((Scheme.ΓSpecIso (.of A)).hom s)
  exact hfirst.trans (hsecond.trans hthird)

variable [IsAlgClosed K]

private theorem polynomial_zero_product (A : Type u) [CommRing A] [Algebra K A]
    [IsDomain A] [Algebra.FiniteType K A] :
    ((affineMorphism (evalZero (K := K) A) ≫
      (algebraIso (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A)).hom) ≫
        (affineTensorIso K A (SymmetricAlgebra K K)).hom) =
      lift (𝟙 (affineVariety K A).toOver) (toUnit (affineVariety K A).toOver ≫
        (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) := by
  let f : SymmetricAlgebra K K →ₐ[K] A :=
    ((evalZero (K := K) A).comp
      (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K) A).toAlgHom).comp
        Algebra.TensorProduct.includeRight
  have hright : affineMorphism f = toUnit (affineVariety K A).toOver ≫
      (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0) := by
    apply Variety.mapPoints_injective (X := affineVariety K A) (Y := additiveVariety K)
    funext x
    obtain ⟨p, rfl⟩ := ((affineVarietyPointsEquiv K A).symm).surjective x
    exact (coordinate_points f p 0
      ((congrArg p (zero_generator (K := K) A)).trans (map_zero p))).trans
        (constant_zero_points (affineVariety K A) _).symm
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, affineTensorIso_fst, algebraIso_hom, affine_comp,
      zero_left, affine_id, lift_fst]
  · simpa only [Category.assoc, affineTensorIso_snd, algebraIso_hom, affine_comp, lift_snd] using
    hright

private theorem section_chain {S : Scheme} {X Y Z W V : Over S}
    (e : X ≅ Y) (f : Y ≅ Z) (g : Z ≅ W) (q : W ⟶ V)
    (u : X ⟶ V) (hu : u = (e ≪≫ f ≪≫ g).hom ≫ q)
    (t : Y ⟶ V) (ht : f.hom ≫ (g.hom ≫ q) = t)
    (s : Γ(V.left, ⊤)) :
    u.left.appTop s = e.hom.left.appTop (t.left.appTop s) := by
  have hmap : u = e.hom ≫ t := hu.trans
    ((iso_chart_comp e f g q).trans (congrArg (e.hom ≫ ·) ht))
  exact (SchubertGeometry.DeterminantSection.appTop_of_eq hmap s).trans
    (SchubertGeometry.DeterminantSection.over_appTop_comp e.hom t s)

omit [IsAlgClosed K] in
private theorem value_section_chain {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    {Z W V : Over (Spec (CommRingCat.of K))}
    (e : A ≃ₐ[K] B) (f : (affineVariety K A).toOver ≅ Z) (g : Z ≅ W) (q : W ⟶ V)
    (u : (affineVariety K B).toOver ⟶ V)
    (hu : u = (algebraIso e ≪≫ f ≪≫ g).hom ≫ q)
    (t : (affineVariety K A).toOver ⟶ V) (ht : f.hom ≫ (g.hom ≫ q) = t)
    (s : Γ(V.left, ⊤)) (b : B)
    (hb : b = e ((Scheme.ΓSpecIso (.of A)).hom (t.left.appTop s))) :
    u.left.appTop s = affineSection (K := K) B b := by
  have hfirst := section_chain (algebraIso e) f g q u hu t ht s
  have hsecond := algebraIso_section e (t.left.appTop s)
  exact hfirst.trans (hsecond.trans (congrArg (Scheme.ΓSpecIso (.of B)).inv hb.symm))

variable [CharZero K] (G : ReductiveGroupData K)

/-- The full transverse chart has polynomial coordinates over its complementary root algebra. -/
def oppositionPolynomialIso (i : G.rootBase.support) :
    (affineVariety K (Polynomial (G.rootSubsetAlgebra
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))))).toOver ≅
      (oppositeUnipotentVariety G).toOver :=
  algebraIso (SchubertGeometry.DeterminantSection.tensorPolynomial
    (SchubertGeometry.DeterminantSection.chartAlgebra G i)) ≪≫
      affineTensorIso K (SchubertGeometry.DeterminantSection.chartAlgebra G i) (SymmetricAlgebra K
        K) ≪≫
        oppositeSimpleCoordinates G i

/-- The opposition polynomial chart maps to the flag variety. -/
def oppositionPolynomialMap (i : G.rootBase.support) :
    (affineVariety K (Polynomial (G.rootSubsetAlgebra
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))))).toOver ⟶
      (flagVariety G).toOver :=
  (oppositionPolynomialIso G i).hom ≫ flagChartMorphism G (oppositionChartPoint G i)

/-- The opposition polynomial chart is an open immersion into the flag variety. -/
instance oppositionPolynomialMap_open (i : G.rootBase.support) :
    IsOpenImmersion (oppositionPolynomialMap G i).left := by
  change IsOpenImmersion ((oppositionPolynomialIso G i).hom.left ≫
    (flagChartMorphism G (oppositionChartPoint G i)).left)
  infer_instance

/-- Polynomial evaluation at zero is the zero section of the transverse chart. -/
theorem oppositionPolynomialIso_zero (i : G.rootBase.support) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom
      (0 : SchubertGeometry.DeterminantSection.chartAlgebra G i))) ≫
      (oppositionPolynomialIso G i).hom.left = (oppositionZeroMap G i).left := by
  have h := compose_iso_zero
    (affineMorphism (evalZero (SchubertGeometry.DeterminantSection.chartAlgebra G i)))
    (algebraIso (SchubertGeometry.DeterminantSection.tensorPolynomial
      (SchubertGeometry.DeterminantSection.chartAlgebra G i)))
    (affineTensorIso K (SchubertGeometry.DeterminantSection.chartAlgebra G i) (SymmetricAlgebra K
      K))
    (oppositeSimpleCoordinates G i) _
    (polynomial_zero_product (SchubertGeometry.DeterminantSection.chartAlgebra G i))
  exact zero_left_transport _ (oppositionPolynomialIso G i) (oppositionZeroMap G i) _
    (evalZero_spec (SchubertGeometry.DeterminantSection.chartAlgebra G i)) h

private def tailMap (i : G.rootBase.support) :=
  (affineTensorIso K (SchubertGeometry.DeterminantSection.chartAlgebra G i) (SymmetricAlgebra K
    K)).hom ≫ ((oppositeSimpleCoordinates G i).hom ≫ (flagChartMap G (oppositionChartPoint G i)))

private theorem tailMap_eq (i : G.rootBase.support) :
    tailMap G i = SchubertGeometry.DeterminantSection.tensorChart G i := rfl

private theorem value_eq (i : G.rootBase.support) (N : ℕ) :
    oppositionChartPolynomial G i N =
      SchubertGeometry.DeterminantSection.tensorPolynomial (K := K)
        (SchubertGeometry.DeterminantSection.chartAlgebra G i)
        ((Scheme.ΓSpecIso (.of (SchubertGeometry.DeterminantSection.chartAlgebra G i ⊗[K]
          SymmetricAlgebra K K))).hom
          ((SchubertGeometry.DeterminantSection.tensorChart G i).left.appTop
            (positiveDetPowerFunction G N))) := rfl

/-- Polynomial coordinates pull back the original regular coefficient to its transverse polynomial.
  -/
theorem oppositionPolynomialIso_function (i : G.rootBase.support) (N : ℕ) :
    ((oppositionPolynomialIso G i).hom ≫ flagChartMap G (oppositionChartPoint G i)).left.appTop
      (positiveDetPowerFunction G N) =
      affineSection (K := K) (Polynomial (G.rootSubsetAlgebra
        {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)}
        (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)))) (oppositionChartPolynomial G i N) := by
  exact value_section_chain (B := Polynomial (G.rootSubsetAlgebra
        {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)}
        (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i))))
    (SchubertGeometry.DeterminantSection.tensorPolynomial (K := K)
      (SchubertGeometry.DeterminantSection.chartAlgebra G i))
    (affineTensorIso K (SchubertGeometry.DeterminantSection.chartAlgebra G i)
      (SymmetricAlgebra K K))
    (oppositeSimpleCoordinates G i) (flagChartMap G (oppositionChartPoint G i))
    ((oppositionPolynomialIso G i).hom ≫ flagChartMap G (oppositionChartPoint G i)) rfl
    (SchubertGeometry.DeterminantSection.tensorChart G i) (tailMap_eq G i)
    (positiveDetPowerFunction G N) (oppositionChartPolynomial G i N) (value_eq G i N)

end SchubertGeometry.DeterminantSection
