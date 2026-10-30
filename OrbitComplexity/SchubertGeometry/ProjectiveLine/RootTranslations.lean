import OrbitComplexity.SchubertGeometry.ProjectiveLine.PolynomialChart
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms

/-! # The chosen root action and projective translations -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti Topology
universe u
variable {K : Type u} [Field K]

private def gaPolynomialMorphism :
    (additiveVariety K).toOver ⟶ (affineVariety K (Polynomial K)).toOver :=
  affineMorphism (Polynomial.aeval (SymmetricAlgebra.ι K K 1))

private theorem gaPolynomial_points (t : K) :
    Variety.mapPoints (gaPolynomialMorphism (K := K)) (additivePointsEquiv K t) =
      (affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval t) := by
  let p := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  change Variety.mapPoints (affineMorphism (Polynomial.aeval (SymmetricAlgebra.ι K K 1)))
      ((affineVarietyPointsEquiv K _).symm p) = _
  rw [affineMorphism_points]
  apply (affineVarietyPointsEquiv K (Polynomial K)).injective
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Polynomial.algHom_ext
  change p ((Polynomial.aeval (SymmetricAlgebra.ι K K 1)) Polynomial.X) =
    (Polynomial.aeval t) Polynomial.X
  rw [Polynomial.aeval_X, Polynomial.aeval_X]
  exact AdditiveGroup.gaPointsMulEquiv_symm_apply_ι (Multiplicative.ofAdd t)

private theorem polynomialTranslation_points (a t : K) :
    Variety.mapPoints (affineMorphism (Polynomial.algEquivAevalXAddC a).toAlgHom)
      ((affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval t)) =
    (affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval (a + t)) := by
  rw [affineMorphism_points]
  congr 1
  apply Polynomial.algHom_ext
  change (Polynomial.aeval t) (Polynomial.algEquivAevalXAddC a Polynomial.X) =
    (Polynomial.aeval (a + t)) Polynomial.X
  simp [add_comm]

private theorem additivePoint_add (a t : K) :
    additivePointsEquiv K (a + t) = additivePointsEquiv K a * additivePointsEquiv K t := by
  change affineGroupPointsMulEquiv K (SymmetricAlgebra K K)
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd a * Multiplicative.ofAdd t)) = _
  rw [map_mul, map_mul]
  rfl

variable [IsAlgClosed K]

private theorem gaPolynomial_translation (a : K) :
    (leftTranslation (additiveVariety K) (additivePointsEquiv K a)).hom ≫
      gaPolynomialMorphism =
    gaPolynomialMorphism ≫ affineMorphism (Polynomial.algEquivAevalXAddC a).toAlgHom := by
  apply Variety.mapPoints_injective
  funext q
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective q
  simp only [Variety.mapPoints_comp, leftTranslation_points]
  rw [← additivePoint_add, gaPolynomial_points, gaPolynomial_points,
    polynomialTranslation_points]

private def projectiveTranslationOver (a : K) :
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver ≅
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  Over.isoMk (projectiveLineTranslationIso a) (projectiveLineTranslation_base a)

private theorem factor_translation {A B C : Scheme.{u}}
    (j : A ⟶ C) (q : A ⟶ B) (c : B ⟶ C)
    (l : A ⟶ A) (s : B ⟶ B) (m : C ⟶ C)
    (hj : j = q ≫ c) (hq : l ≫ q = q ≫ s) (hc : s ≫ c = c ≫ m) :
    j ≫ m = l ≫ j := by
  rw [hj, Category.assoc, ← hc, ← Category.assoc, ← hq, Category.assoc]

private theorem projectiveGaChart_translation (a : K) :
    projectiveLineChart K ⟨0⟩ ≫ (projectiveTranslationOver a).hom =
      (leftTranslation (additiveVariety K) (additivePointsEquiv K a)).hom ≫
        projectiveLineChart K ⟨0⟩ := by
  have h := congrArg Over.Hom.left (gaPolynomial_translation a)
  change (leftTranslation (additiveVariety K) (additivePointsEquiv K a)).hom.left ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (SymmetricAlgebra.ι K K 1)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC a).toRingHom) at h
  apply Over.OverMorphism.ext
  exact factor_translation _ _ _ _ _ _ (projectiveLineChart_polynomial K ⟨0⟩) h
    (projectiveLineTranslation_chart a)

private theorem eq_of_open_chart {X Y : Variety K} [PreirreducibleSpace X.scheme]
    (c : (additiveVariety K).toOver ⟶ X.toOver) [IsOpenImmersion c.left]
    (f g : X.toOver ⟶ Y.toOver) (he : c ≫ f = c ≫ g) : f = g := by
  have hf : f.left ≫ Y.toSpec = X.toSpec := f.w
  have hg : g.left ≫ Y.toSpec = X.toSpec := g.w
  have : LocallyOfFiniteType (f.left ≫ Y.toSpec) := by rw [hf]; infer_instance
  have : IsReduced X.toOver.left := X.reduced
  have : PreirreducibleSpace X.toOver.left := inferInstanceAs (PreirreducibleSpace X.scheme)
  have hne : (Set.range c.left).Nonempty :=
    ⟨c.left ((additiveVariety K).pointMap (additivePointsEquiv K 0)), _, rfl⟩
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq Y.toSpec (Set.range c.left)
    c.left.isOpenEmbedding.2.isLocallyClosed (c.left.isOpenEmbedding.2.dense hne)
  · rintro x ⟨z, rfl⟩ _
    exact congrArg (fun k => k z) (congrArg Over.Hom.left he)
  · exact hf.trans hg.symm

private theorem chartAction_transport {X P : Variety K} [PreirreducibleSpace X.scheme]
    (c : (additiveVariety K).toOver ⟶ X.toOver) [IsOpenImmersion c.left]
    (d : (additiveVariety K).toOver ⟶ P.toOver) (e : X.toOver ≅ P.toOver)
    (a : K) (f : X.toOver ⟶ X.toOver) (g : P.toOver ⟶ P.toOver)
    (hce : c ≫ e.hom = d)
    (hf : c ≫ f = (leftTranslation (additiveVariety K) (additivePointsEquiv K a)).hom ≫ c)
    (hg : d ≫ g = (leftTranslation (additiveVariety K) (additivePointsEquiv K a)).hom ≫ d) :
    f ≫ e.hom = e.hom ≫ g := by
  apply eq_of_open_chart c
  rw [← Category.assoc, hf, Category.assoc, hce, ← hg,
    ← hce, Category.assoc]

variable [CharZero K] (G : ReductiveGroupData K)

private def gaLeviPoint (i : G.rootBase.support) (a : K) : (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨gaParameterPoint (G.simpleRootMap i) a, G.simpleRootPoint_mem_levi {i} i (by simp) a⟩

/-- The chosen positive root acts on the projective line by its triangular translation. -/
theorem simpleSchubertIso_ga (i : G.rootBase.support) (a : K) :
    type_of% (chartAction_transport (simplePositiveChart G i) (projectiveLineChart K ⟨0⟩)
      (simpleSchubertIso G i) a
      (Variety.translateMorphism (leviVariety G {i})
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) (gaLeviPoint G i a))
      (projectiveTranslationOver a).hom (simpleSchubertIso_positive G i)
      (simplePositiveChart_ga G i a) (projectiveGaChart_translation a)) :=
  chartAction_transport (simplePositiveChart G i) (projectiveLineChart K ⟨0⟩)
    (simpleSchubertIso G i) a
    (Variety.translateMorphism (leviVariety G {i})
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) (gaLeviPoint G i a))
    (projectiveTranslationOver a).hom (simpleSchubertIso_positive G i)
    (simplePositiveChart_ga G i a) (projectiveGaChart_translation a)

end SchubertGeometry
