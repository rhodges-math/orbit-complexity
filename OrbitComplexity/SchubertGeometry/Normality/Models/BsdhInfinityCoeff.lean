import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveChartTransitions
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveLine

/-! # Infinity in the specified simple-line product coordinates -/

noncomputable section
namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory

universe u

private theorem polynomial_chart (R : Type u) [CommRing R] (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart R j =
      Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom) ≫
          projectiveChartMap R (ULift.{u} (Fin 2)) j := rfl

private theorem unique_map (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (σ : Type u) [Unique σ] :
    (MvPolynomial.uniqueAlgEquiv R σ).toRingHom.comp (MvPolynomial.map f) =
      (Polynomial.mapRingHom f).comp (MvPolynomial.uniqueAlgEquiv S σ).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro s
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.map f (MvPolynomial.C s)) =
      Polynomial.map f (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.C s))
    simp only [MvPolynomial.map_C, MvPolynomial.eval₂_C, Polynomial.map_C]
  · intro i
    change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.map f (MvPolynomial.X i)) =
      Polynomial.map f (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.X i))
    simp only [MvPolynomial.map_X, MvPolynomial.eval₂_X, Polynomial.map_X]

private theorem polynomial_coeff (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (j : ULift.{u} (Fin 2)) :
    projectiveLinePolynomialChart R j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        projectiveLinePolynomialChart S j := by
  have hc : CommRingCat.ofHom (MvPolynomial.map f) ≫
      CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom =
      CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv S
        {i : ULift.{u} (Fin 2) // i ≠ j}).toRingHom ≫
      CommRingCat.ofHom (Polynomial.mapRingHom f) := by
    apply CommRingCat.hom_ext
    exact unique_map S R f {i : ULift.{u} (Fin 2) // i ≠ j}
  have hs := congrArg (fun h => Spec.map h) hc
  simp only [Spec.map_comp] at hs
  rw [polynomial_chart, polynomial_chart, Category.assoc, projectiveCoeffMap_chart,
    ← Category.assoc, hs, Category.assoc]

private theorem section_coeff (S R : Type u) [CommRing S] [CommRing R]
    (f : S →+* R) (j : ULift.{u} (Fin 2)) :
    projectiveLineSection R j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom f) ≫ projectiveLineSection S j := by
  rw [projectiveLineSection, Category.assoc, polynomial_coeff, ← Category.assoc,
    ← Spec.map_comp, projectiveLineSection, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext <;> simp

private theorem section_base (R : Type u) [CommRing R] (j : ULift.{u} (Fin 2)) :
    projectiveLineSection R j ≫ projectiveToSpec R (ULift.{u} (Fin 2)) = 𝟙 _ := by
  rw [projectiveLineSection, Category.assoc, projectiveLinePolynomialChart_base,
    ← Spec.map_comp]
  rw [show CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
    CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 (CommRingCat.of R) from by
      ext r
      simp]
  exact Spec.map_id _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Both product projections carry infinity to the specified simple-line zero section. -/
theorem simple_infinity_product (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    let S := (algSpec (.of K)).obj (.op A)
    let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
    (projectiveLineSection A ⟨1⟩ ≫ (simpleBorelLineIso G i A).inv ≫
        (fst S Y).left = 𝟙 _) ∧
      (projectiveLineSection A ⟨1⟩ ≫ (simpleBorelLineIso G i A).inv ≫
        (snd S Y).left =
          Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ projectiveLineSection K ⟨1⟩ ≫
            (simpleSchubertIso G i).inv.left) := by
  dsimp only
  let S := (algSpec (.of K)).obj (.op A)
  let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  let P := (projectiveVariety K (ULift.{u} (Fin 2))).toOver
  let e := projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)
  let t := tensorIso (Iso.refl S) (simpleSchubertIso G i).symm
  have he : (simpleBorelLineIso G i A).inv = e.hom ≫ t.hom.left := rfl
  have ht₁ : t.hom.left ≫ (fst S Y).left = (fst S P).left := by
    have h : t.hom ≫ fst S Y = fst S P := by
      change (𝟙 S ⊗ₘ (simpleSchubertIso G i).inv) ≫ fst S Y = _
      rw [tensorHom_fst, Category.comp_id]
    exact congrArg Over.Hom.left h
  have ht₂ : t.hom.left ≫ (snd S Y).left =
      (snd S P).left ≫ (simpleSchubertIso G i).inv.left := by
    have h : t.hom ≫ snd S Y = snd S P ≫ (simpleSchubertIso G i).inv := by
      change (𝟙 S ⊗ₘ (simpleSchubertIso G i).inv) ≫ snd S Y = _
      exact tensorHom_snd _ _
    exact congrArg Over.Hom.left h
  have hf : (simpleBorelLineIso G i A).inv ≫ (fst S Y).left =
      projectiveToSpec A (ULift.{u} (Fin 2)) := by
    have hb : e.hom ≫ (fst S P).left = projectiveToSpec A (ULift.{u} (Fin 2)) :=
      projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap K A)
    exact (congrArg (fun f ↦ f ≫ (fst S Y).left) he).trans
      ((Category.assoc e.hom t.hom.left (fst S Y).left).trans
        ((congrArg (fun f ↦ e.hom ≫ f) ht₁).trans hb))
  have hs : (simpleBorelLineIso G i A).inv ≫ (snd S Y).left =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A) ≫
        (simpleSchubertIso G i).inv.left := by
    have hb : e.hom ≫ (snd S P).left =
        projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A) :=
      projectiveBaseChange_snd (ULift.{u} (Fin 2)) (algebraMap K A)
    have hb' : e.hom ≫ ((snd S P).left ≫ (simpleSchubertIso G i).inv.left) =
        projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A) ≫
          (simpleSchubertIso G i).inv.left :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ f ≫ (simpleSchubertIso G i).inv.left) hb)
    exact (congrArg (fun f ↦ f ≫ (snd S Y).left) he).trans
      ((Category.assoc e.hom t.hom.left (snd S Y).left).trans
        ((congrArg (fun f ↦ e.hom ≫ f) ht₂).trans hb'))
  constructor
  · exact (congrArg (fun f ↦ projectiveLineSection A ⟨1⟩ ≫ f) hf).trans
      (section_base A ⟨1⟩)
  · calc
      _ = projectiveLineSection A ⟨1⟩ ≫
          (projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A) ≫
            (simpleSchubertIso G i).inv.left) :=
        congrArg (fun f ↦ projectiveLineSection A ⟨1⟩ ≫ f) hs
      _ = (projectiveLineSection A ⟨1⟩ ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) (algebraMap K A)) ≫
            (simpleSchubertIso G i).inv.left := (Category.assoc _ _ _).symm
      _ = _ := (congrArg (fun f ↦ f ≫ (simpleSchubertIso G i).inv.left)
        (section_coeff K A (algebraMap K A) ⟨1⟩)).trans (Category.assoc _ _ _)

end SchubertGeometry
