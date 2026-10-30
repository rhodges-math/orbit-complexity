import OrbitComplexity.GroupActions.Representations.ProjectiveMatrixPoints
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Regular families of projective matrix maps

A matrix unit over an affine coordinate algebra defines a regular map from the product
of its affine variety and projective space. Coefficient evaluation specializes the matrix.
-/

noncomputable section
namespace GroupActions
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CartesianMonoidalCategory MonoidalCategory
universe u
variable {K H ι : Type u} [Field K] [CommRing H] [Algebra K H]
  [Fintype ι] [DecidableEq ι]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem matrix_specialize (a : Matrix.GeneralLinearGroup ι H) (g : H →ₐ[K] K) :
    projectiveCoeffMap ι g.toRingHom ≫ projectiveMatrixMap (R := K) a =
      projectiveMatrixMap (R := K) (Matrix.GeneralLinearGroup.map g.toRingHom a) := by
  unfold projectiveCoeffMap projectiveMatrixMap
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change MvPolynomial.map g.toRingHom
        (projectiveMatrixHom (a : Matrix ι ι H) (C r)) =
      projectiveMatrixHom ((Matrix.GeneralLinearGroup.map g.toRingHom a :
        Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) (C r)
    rw [projectiveMatrixHom_C, MvPolynomial.map_C, projectiveMatrixHom_C]
    exact congrArg C (g.commutes r)
  · intro i
    change MvPolynomial.map g.toRingHom
        (projectiveMatrixHom (a : Matrix ι ι H) (X i)) =
      projectiveMatrixHom ((Matrix.GeneralLinearGroup.map g.toRingHom a :
        Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) (X i)
    simp only [projectiveMatrixHom_X, map_sum, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_X, Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe]


omit [DecidableEq ι] in
private theorem coeff_base {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    projectiveCoeffMap ι f ≫ projectiveToSpec R ι =
      projectiveToSpec S ι ≫ Spec.map (CommRingCat.ofHom f) := by
  let e := projectiveBaseChange ι f
  calc
    projectiveCoeffMap ι f ≫ projectiveToSpec R ι =
        (e.hom ≫ pullback.snd _ _) ≫ projectiveToSpec R ι := by
      rw [projectiveBaseChange_snd]
    _ = e.hom ≫ pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom f) := by
      rw [Category.assoc, ← pullback.condition]
    _ = projectiveToSpec S ι ≫ Spec.map (CommRingCat.ofHom f) := by
      rw [← Category.assoc, projectiveBaseChange_fst]

omit [Fintype ι] [DecidableEq ι] in
private theorem coeff_retraction (g : H →ₐ[K] K) :
    projectiveCoeffMap ι g.toRingHom ≫ projectiveCoeffMap ι (algebraMap K H) = 𝟙 _ := by
  unfold projectiveCoeffMap
  rw [← Proj.map_comp, ← (Proj.map_id (𝒜 := homogeneousSubmodule ι K))]
  congr 1
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change MvPolynomial.map g.toRingHom (MvPolynomial.map (algebraMap K H) (C r)) = C r
    rw [MvPolynomial.map_C, MvPolynomial.map_C]
    change C (g (algebraMap K H r)) = C r
    rw [g.commutes, Algebra.algebraMap_self_apply]
  · intro i
    change MvPolynomial.map g.toRingHom (MvPolynomial.map (algebraMap K H) (X i)) = X i
    rw [MvPolynomial.map_X, MvPolynomial.map_X]

omit [Fintype ι] [DecidableEq ι] in
private theorem point_square (g : H →ₐ[K] K)
    (q : Spec (CommRingCat.of K) ⟶ projectiveScheme K ι)
    (hq : q ≫ projectiveToSpec K ι = 𝟙 _) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K H)) = q ≫ projectiveToSpec K ι := by
  rw [hq, ← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K H) ≫ CommRingCat.ofHom g.toRingHom =
      𝟙 (CommRingCat.of K) := by
    ext r
    exact g.commutes r
  rw [he, Spec.map_id]

omit [DecidableEq ι] in
private theorem basechange_pair (g : H →ₐ[K] K)
    (q : Spec (CommRingCat.of K) ⟶ projectiveScheme K ι)
    (hq : q ≫ projectiveToSpec K ι = 𝟙 _) :
    pullback.lift (Spec.map (CommRingCat.ofHom g.toRingHom)) q (point_square g q hq) ≫
      (projectiveBaseChange ι (algebraMap K H)).inv =
        q ≫ projectiveCoeffMap ι g.toRingHom := by
  apply (cancel_mono (projectiveBaseChange ι (algebraMap K H)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, projectiveBaseChange_fst, Category.assoc,
      coeff_base, ← Category.assoc, hq, Category.id_comp]
  · rw [pullback.lift_snd, Category.assoc, projectiveBaseChange_snd, Category.assoc,
      coeff_retraction, Category.comp_id]

variable [IsReduced H] [Algebra.FiniteType K H]

/-- A matrix over an affine algebra defines a regular family of projective maps. -/
def projectiveMatrixFamily (a : Matrix.GeneralLinearGroup ι H) :
    (affineVariety K H).toOver ⊗ (projectiveVariety K ι).toOver ⟶
      (projectiveVariety K ι).toOver :=
  Over.homMk ((projectiveBaseChange ι (algebraMap K H)).inv ≫ projectiveMatrixMap a) (by
    change ((projectiveBaseChange ι (algebraMap K H)).inv ≫ projectiveMatrixMap a) ≫
        projectiveToSpec K ι = _
    rw [Category.assoc, projectiveMatrixMap_toSpec, ← Category.assoc]
    have he : (projectiveBaseChange ι (algebraMap K H)).inv ≫ projectiveToSpec H ι =
        pullback.fst _ _ := by
      rw [Iso.inv_comp_eq, projectiveBaseChange_fst]
    rw [he]
    rfl)

/-- Evaluation at an affine rational point specializes the projective matrix. -/
theorem projectiveMatrixFamily_points (a : Matrix.GeneralLinearGroup ι H) (g : H →ₐ[K] K)
    (p : (projectiveVariety K ι).points) :
    lift ((affineVariety K H).pointsEquivOverHom (affinePointsEquiv g))
        ((projectiveVariety K ι).pointsEquivOverHom p) ≫ projectiveMatrixFamily a =
      (projectiveVariety K ι).pointsEquivOverHom p ≫
        projectiveMatrixMorphism (Matrix.GeneralLinearGroup.map g.toRingHom a) := by
  apply Over.OverMorphism.ext
  let q : Spec (CommRingCat.of K) ⟶ projectiveScheme K ι := p.val
  have hq : q ≫ projectiveToSpec K ι = 𝟙 _ := p.property
  change pullback.lift (Spec.map (CommRingCat.ofHom g.toRingHom)) q (point_square g q hq) ≫
      ((projectiveBaseChange ι (algebraMap K H)).inv ≫ projectiveMatrixMap a) =
    q ≫ projectiveMatrixMap (Matrix.GeneralLinearGroup.map g.toRingHom a)
  rw [← Category.assoc, basechange_pair g q hq, Category.assoc, matrix_specialize]

end GroupActions
