import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveChartTransitions

/-! # Coefficient naturality of the specified append chart -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry
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


private theorem tensor_natural {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {A B Y P : C} (f : B ⟶ A) (e : Y ≅ P) :
    (f ⊗ₘ 𝟙 Y) ≫ (𝟙 A ⊗ₘ e.hom) = (𝟙 B ⊗ₘ e.hom) ≫ (f ⊗ₘ 𝟙 P) := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

private theorem inverse_square {C : Type v} [Category.{w} C]
    {X Y A B V W : C} (eA : X ≅ Y) (eB : A ≅ B) (f : A ⟶ X) (g : B ⟶ Y)
    (p : W ⟶ B) (q : V ⟶ Y) (t : W ⟶ V)
    (ht : f ≫ eA.hom = eB.hom ≫ g) (hb : p ≫ g = t ≫ q) :
    t ≫ (q ≫ eA.inv) = (p ≫ eB.inv) ≫ f := by
  apply (cancel_mono eA.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ht]
  simp only [Iso.inv_hom_id_assoc]
  exact hb.symm

private theorem tensor_comp_tail {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {A B V Y T : C} (f : A ⟶ B) (p : B ⟶ V) (c : V ⊗ Y ⟶ T) :
    (f ⊗ₘ 𝟙 Y) ≫ (p ⊗ₘ 𝟙 Y) ≫ c = ((f ≫ p) ⊗ₘ 𝟙 Y) ≫ c := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

private theorem lineIso_coeff {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A B : CommAlgCat.{u} K)
    (h : A →ₐ[K] B) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) h.toRingHom ≫ (simpleBorelLineIso G i A).inv =
      (simpleBorelLineIso G i B).inv ≫
        ((algSpec (.of K)).map (CommAlgCat.ofHom h).op ⊗ₘ
          𝟙 (schubertVariety G
            (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left := by
  let SA := (algSpec (.of K)).obj (.op A)
  let SB := (algSpec (.of K)).obj (.op B)
  let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  let P := Over.mk (projectiveToSpec K (ULift.{u} (Fin 2)))
  let TA := (Over.forget (Spec (.of K))).mapIso
    (tensorIso (Iso.refl SA) (simpleSchubertIso G i))
  let TB := (Over.forget (Spec (.of K))).mapIso
    (tensorIso (Iso.refl SB) (simpleSchubertIso G i))
  let f := coefficientOver h
  have ht : (f ⊗ₘ 𝟙 Y).left ≫ TA.hom = TB.hom ≫ (f ⊗ₘ 𝟙 P).left :=
    congrArg Over.Hom.left (tensor_natural f (simpleSchubertIso G i))
  exact inverse_square TA TB (f ⊗ₘ 𝟙 Y).left (f ⊗ₘ 𝟙 P).left
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K B)).hom
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)).hom
    (projectiveCoeffMap (ULift.{u} (Fin 2)) h.toRingHom) ht (baseChange_tensor h)

/-- The same specified append chart commutes with every affine coefficient restriction. -/
theorem projectiveAppendChart_coeff {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A B : CommAlgCat.{u} K)
    (h : A →ₐ[K] B) {V T : Over (Spec (.of K))}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) h.toRingHom ≫ projectiveAppendChart G i A p c =
      projectiveAppendChart G i B ((algSpec (.of K)).map (CommAlgCat.ofHom h).op ≫ p) c := by
  rw [projectiveAppendChart, ← Category.assoc, lineIso_coeff, Category.assoc]
  change (simpleBorelLineIso G i B).inv ≫
    (((algSpec (.of K)).map (CommAlgCat.ofHom h).op ⊗ₘ 𝟙 _) ≫ (p ⊗ₘ 𝟙 _) ≫ c).left =
      (simpleBorelLineIso G i B).inv ≫
        ((((algSpec (.of K)).map (CommAlgCat.ofHom h).op ≫ p) ⊗ₘ 𝟙 _) ≫ c).left
  exact congrArg (fun m ↦ (simpleBorelLineIso G i B).inv ≫ m.left)
    (tensor_comp_tail ((algSpec (.of K)).map (CommAlgCat.ofHom h).op) p c)

end SchubertGeometry
