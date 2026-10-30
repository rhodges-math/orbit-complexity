import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelPullback
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelLineIso
import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Affine base change of Borel actions -/

namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K R C : Type u} [CommRing K] [CommRing R] [CommRing C]

private theorem coefficient_comp (f : K →+* R) (g : R →+* C) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) g ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (g.comp f) := by
  unfold projectiveCoeffMap
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  change (MvPolynomial.map g).comp (MvPolynomial.map f) = MvPolynomial.map (g.comp f)
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

private theorem coefficient_base (f : R →+* C) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec C (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← projectiveBaseChange_snd (ULift.{u} (Fin 2)) f, Category.assoc,
    ← pullback.condition, ← Category.assoc, projectiveBaseChange_fst]

variable [Algebra K R] [Algebra K C]

private def coefficientOver (f : R →ₐ[K] C) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)) =
        Spec.map (CommRingCat.ofHom (algebraMap K C))
    rw [← Spec.map_comp]
    congr 1
    ext k
    exact f.commutes k)

private theorem coefficientOver_fst (f : R →ₐ[K] C) :
    (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (projectiveToSpec K (ULift.{u} (Fin 2))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K C)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  have h := congrArg Over.Hom.left (tensorHom_fst (coefficientOver f)
    (𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))))
  change (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K R)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K C)))
      (projectiveToSpec K (ULift.{u} (Fin 2))) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) at h
  exact h

private theorem coefficientOver_snd (f : R →ₐ[K] C) :
    (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (projectiveToSpec K (ULift.{u} (Fin 2))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K C)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) := by
  have h := congrArg Over.Hom.left (tensorHom_snd (coefficientOver f)
    (𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))))
  change (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K R)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K C)))
      (projectiveToSpec K (ULift.{u} (Fin 2))) ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private theorem baseChange_tensor (f : R →ₐ[K] C) :
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom ≫
        (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left =
      projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom := by
  apply pullback.hom_ext
  · change ((projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom ≫
      (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left) ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (projectiveToSpec K (ULift.{u} (Fin 2))) =
      (projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom) ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K R)))
            (projectiveToSpec K (ULift.{u} (Fin 2)))
    rw [Category.assoc, coefficientOver_fst, ← Category.assoc, projectiveBaseChange_fst,
      Category.assoc, projectiveBaseChange_fst]
    exact (coefficient_base f.toRingHom).symm
  · change ((projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom ≫
      (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left) ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K R)))
          (projectiveToSpec K (ULift.{u} (Fin 2))) =
      (projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom) ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K R)))
            (projectiveToSpec K (ULift.{u} (Fin 2)))
    rw [Category.assoc, coefficientOver_snd, projectiveBaseChange_snd,
      Category.assoc, projectiveBaseChange_snd, coefficient_comp]
    congr 1
    ext k
    exact (f.commutes k).symm

private theorem affineFamily_pullback (f : R →ₐ[K] C) (c : Rˣ) (a : R) :
    (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))) ≫
        projectiveAffineFamily (algebraMap K R) c a =
      projectiveAffineFamily (algebraMap K C)
        (Units.map f.toRingHom.toMonoidHom c) (f a) := by
  have hm : f.toRingHom.comp (algebraMap K R) = algebraMap K C := by
    ext k
    exact f.commutes k
  have hc : projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K R) =
        projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K C) :=
    (coefficient_comp (algebraMap K R) f.toRingHom).trans
      (congrArg (projectiveCoeffMap (ULift.{u} (Fin 2))) hm)
  have hb := congrArg (fun m => m ≫ (projectiveAffineFamily (algebraMap K R) c a).left)
    (baseChange_tensor f)
  have ha := congrArg
    (fun m => m ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K R))
    (projectiveAffine_coeff f.toRingHom c a).symm
  apply Over.OverMorphism.ext
  apply (cancel_epi (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom).mp
  change (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom ≫
      (coefficientOver f ⊗ₘ 𝟙 (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))).left ≫
        (projectiveAffineFamily (algebraMap K R) c a).left =
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom ≫
      (projectiveAffineFamily (algebraMap K C)
        (Units.map f.toRingHom.toMonoidHom c) (f a)).left
  calc
    _ = projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom ≫
          (projectiveAffineFamily (algebraMap K R) c a).left := by
      simpa only [Category.assoc] using hb
    _ = projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K R) := by
      change _ ≫ (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).inv ≫ _ = _
      rw [Iso.hom_inv_id_assoc]
    _ = (projectiveLineScalingIso (Units.map f.toRingHom.toMonoidHom c)).hom ≫
        (projectiveLineTranslationIso (f a)).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K C) := by
      change _ = (projectiveLineScalingIso (Units.map f.toRingHom.toMonoidHom c)).hom ≫
        (projectiveLineTranslationIso (f.toRingHom a)).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K C)
      simpa only [Category.assoc, hc] using ha
    _ = _ := by
      change _ = (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).hom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K C)).inv ≫ _
      rw [Iso.hom_inv_id_assoc]

private theorem affineFamily_conjugate (c : Rˣ) (a : R) :
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).hom ≫
      (lift (fst (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R))))
        (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2)))))
        (projectiveAffineFamily (algebraMap K R) c a)).left ≫
      (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).inv =
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom := by
  have h := projectiveAffineFamily_relative (algebraMap K R) c a
  rw [← h]
  rw [← Category.assoc]
  apply congrArg (fun m => m ≫
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K R)).inv)
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.lift_left, pullback.lift_fst, Over.fst_left,
      Over.mk_hom, projectiveBaseChange_fst]
  · simp only [Category.assoc, Over.lift_left, Over.mk_hom, pullback.lift_snd]

universe v w

private theorem tensorFamily_pullback {D : Type v} [Category.{w} D] [MonoidalCategory D]
    {B S X P R : D} (β : S ⟶ B) (q : B ⟶ R) (e : X ≅ P)
    (m : B ⊗ X ⟶ X) (F : R ⊗ P ⟶ P) (f : S ⟶ R) (F' : S ⊗ P ⟶ P)
    (h : (𝟙 B ⊗ₘ e.inv) ≫ m ≫ e.hom = (q ⊗ₘ 𝟙 P) ≫ F)
    (hf : f = β ≫ q) (hF : (f ⊗ₘ 𝟙 P) ≫ F = F') :
    (β ⊗ₘ e.inv) ≫ m ≫ e.hom = F' := by
  rw [hf] at hF
  calc
    _ = (β ⊗ₘ 𝟙 P) ≫ (𝟙 B ⊗ₘ e.inv) ≫ m ≫ e.hom := by
      rw [← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp, Category.assoc]
    _ = (β ⊗ₘ 𝟙 P) ≫ (q ⊗ₘ 𝟙 P) ≫ F := congrArg (fun t => (β ⊗ₘ 𝟙 P) ≫ t) h
    _ = _ := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
      exact hF

private theorem twist_conjugate {D : Type v} [Category.{w} D] [CartesianMonoidalCategory D]
    {H S Y P : D} [GrpObj H] [ModObj H Y] (β : S ⟶ H) (e : Y ≅ P) :
    (𝟙 S ⊗ₘ e.inv) ≫ lift (fst S Y) ((fst S Y ≫ β) • snd S Y) ≫
        (𝟙 S ⊗ₘ e.hom) =
      lift (fst S P) ((β ⊗ₘ e.inv) ≫ ModObj.smul (M := H) (X := Y) ≫ e.hom) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
  · calc
      _ = ((𝟙 S ⊗ₘ e.inv) ≫ ((fst S Y ≫ β) • snd S Y)) ≫ e.hom := by
        simp only [Category.assoc, tensorHom_snd, lift_snd_assoc]
      _ = ((fst S P ≫ β) • (snd S P ≫ e.inv)) ≫ e.hom := by
        congr 1
        rw [ModObj.comp_smul]
        simp only [tensorHom_fst_assoc, tensorHom_snd, Category.id_comp]
      _ = _ := by
        simp only [CategoryTheory.Hom.smul_def, lift_fst_comp_snd_comp, lift_snd,
          Category.assoc]

private theorem twist_family_conjugate {D : Type v} [Category.{w} D]
    [CartesianMonoidalCategory D] {E : Type*} [Category E] (U : D ⥤ E)
    {H S Y P : D} [GrpObj H] [ModObj H Y] (β : S ⟶ H) (e : Y ≅ P)
    {Q : E} (b : Q ≅ U.obj (S ⊗ P)) (F : S ⊗ P ⟶ P)
    (hF : (β ⊗ₘ e.inv) ≫ ModObj.smul (M := H) (X := Y) ≫ e.hom = F)
    (g : Q ⟶ Q) (hg : b.hom ≫ U.map (lift (fst S P) F) ≫ b.inv = g) :
    ((U.mapIso (tensorIso (Iso.refl S) e)) ≪≫ b.symm).inv ≫
      U.map (lift (fst S Y) ((fst S Y ≫ β) • snd S Y)) ≫
        ((U.mapIso (tensorIso (Iso.refl S) e)) ≪≫ b.symm).hom = g := by
  change (b.hom ≫ U.map (𝟙 S ⊗ₘ e.inv)) ≫
    U.map (lift (fst S Y) ((fst S Y ≫ β) • snd S Y)) ≫
      (U.map (𝟙 S ⊗ₘ e.hom) ≫ b.inv) = g
  calc
    _ = b.hom ≫ U.map ((𝟙 S ⊗ₘ e.inv) ≫
      lift (fst S Y) ((fst S Y ≫ β) • snd S Y) ≫ (𝟙 S ⊗ₘ e.hom)) ≫ b.inv := by
      simp only [Functor.map_comp, Category.assoc]
    _ = b.hom ≫ U.map (lift (fst S P) F) ≫ b.inv := by
      rw [twist_conjugate β e, hF]
    _ = g := hg

end
end SchubertGeometry

noncomputable section
namespace SchubertGeometry
open ReductiveGroups CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The coefficient homomorphism of an affine family of Borel elements. -/
def simpleBorelCoefficientMap (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (β : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    simpleBorelCoefficientAlgebra G →ₐ[K] A :=
  ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage
    (show (algSpec (.of K)).obj (.op A) ⟶
        (algSpec (.of K)).obj (.op (CommAlgCat.of K (simpleBorelCoefficientAlgebra G))) from
      β ≫ simpleBorelProjection G i ≫ (simpleBorelTensorIso G i).inv)).unop.hom

private theorem borelCoefficient_spec (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (β : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    coefficientOver (simpleBorelCoefficientMap G i A β) =
      β ≫ simpleBorelProjection G i ≫ (simpleBorelTensorIso G i).inv := by
  have h := (algSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage
    (show (algSpec (.of K)).obj (.op A) ⟶
        (algSpec (.of K)).obj (.op (CommAlgCat.of K (simpleBorelCoefficientAlgebra G))) from
      β ≫ simpleBorelProjection G i ≫ (simpleBorelTensorIso G i).inv)
  exact h




private theorem borelFamily_pullback (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (β : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    letI := simpleBorelAction G i
    (β ⊗ₘ (simpleSchubertIso G i).inv) ≫
      ModObj.smul (M := (borelVariety G).toOver)
        (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
      (simpleSchubertIso G i).hom =
        projectiveAffineFamily (algebraMap K A)
          (Units.map (simpleBorelCoefficientMap G i A β).toRingHom.toMonoidHom
            (simpleRootCoefficient G i))
          ((simpleBorelCoefficientMap G i A β)
            ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
              simpleRootParameter G)) := by
  let := simpleBorelAction G i
  exact tensorFamily_pullback β
    (simpleBorelProjection G i ≫ (simpleBorelTensorIso G i).inv)
    (simpleSchubertIso G i)
    (ModObj.smul (M := (borelVariety G).toOver)
      (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver))
    (projectiveAffineFamily (algebraMap K (simpleBorelCoefficientAlgebra G))
      (simpleRootCoefficient G i)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G))
    (coefficientOver (simpleBorelCoefficientMap G i A β)) _
    (simpleBorel_affine_family G i) (borelCoefficient_spec G i A β)
    (affineFamily_pullback (simpleBorelCoefficientMap G i A β) (simpleRootCoefficient G i)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G))


/-- The Borel action over an affine base is its coefficient-ring affine automorphism. -/
theorem simpleBorelAction_relative (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (β : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    letI := simpleBorelAction G i
    (simpleBorelLineIso G i A).inv ≫
      (lift
        (fst ((algSpec (.of K)).obj (.op A))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver)
        ((fst ((algSpec (.of K)).obj (.op A))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≫ β) •
          snd ((algSpec (.of K)).obj (.op A))
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver)).left ≫
      (simpleBorelLineIso G i A).hom =
        (projectiveLineScalingIso
          (Units.map (simpleBorelCoefficientMap G i A β).toRingHom.toMonoidHom
            (simpleRootCoefficient G i))).hom ≫
        (projectiveLineTranslationIso ((simpleBorelCoefficientMap G i A β)
          ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
            simpleRootParameter G))).hom := by
  let := simpleBorelAction G i
  exact twist_family_conjugate (Over.forget (Spec (.of K))) β (simpleSchubertIso G i)
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A))
    (projectiveAffineFamily (algebraMap K A)
      (Units.map (simpleBorelCoefficientMap G i A β).toRingHom.toMonoidHom
        (simpleRootCoefficient G i))
      ((simpleBorelCoefficientMap G i A β)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
          simpleRootParameter G))) (borelFamily_pullback G i A β) _
    (affineFamily_conjugate
      (Units.map (simpleBorelCoefficientMap G i A β).toRingHom.toMonoidHom
        (simpleRootCoefficient G i))
      ((simpleBorelCoefficientMap G i A β)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)))

end SchubertGeometry
end
