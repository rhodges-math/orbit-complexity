import OrbitComplexity.SchubertGeometry.Normality.Bundles.InfinityDiagramData
import OrbitComplexity.SchubertGeometry.Normality.Models.IntegralProjectiveCoeff
import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineInfinity

/-! # Arithmetic infinity sections and their specified colimit maps -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem infinity_coeff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    projectiveLineSection S (⟨1⟩ : ULift.{u} (Fin 2)) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom f) ≫ projectiveLineSection R ⟨1⟩ := by
  rw [projectiveLineSection, Category.assoc, projectiveLinePolynomial_coeff,
    ← Category.assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (Polynomial.mapRingHom f) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)) =
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) ≫ CommRingCat.ofHom f from by
    apply CommRingCat.hom_ext
    change (Polynomial.evalRingHom (0 : S)).comp (Polynomial.mapRingHom f) =
      f.comp (Polynomial.evalRingHom (0 : R))
    ext x <;> simp]
  simp only [Spec.map_comp, Category.assoc, projectiveLineSection]

private theorem infinity_base {R : Type u} [CommRing R] :
    projectiveLineSection R (⟨1⟩ : ULift.{u} (Fin 2)) ≫
      projectiveToSpec R (ULift.{u} (Fin 2)) = 𝟙 _ := by
  rw [projectiveLineSection, Category.assoc, projectiveLinePolynomialChart_base,
    ← Spec.map_comp]
  rw [show CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 (CommRingCat.of R) from by
    ext r
    simp]
  exact Spec.map_id _

private theorem infinity_transport {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (c : Sˣ) (a : S) :
    projectiveLineSection S (⟨1⟩ : ULift.{u} (Fin 2)) ≫
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom f) ≫ projectiveLineSection R ⟨1⟩ := by
  calc
    _ = (projectiveLineSection S (⟨1⟩ : ULift.{u} (Fin 2)) ≫
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f := by simp only [Category.assoc]
    _ = _ := by rw [ProjectiveLine.projectiveInfinity_affine, infinity_coeff]

private theorem infinity_natural {R S : Type u} [CommRing R] [CommRing S]
    {X Y : Scheme.{u}} (eX : X ≅ projectiveScheme S (ULift.{u} (Fin 2)))
    (eY : Y ≅ projectiveScheme R (ULift.{u} (Fin 2))) (d : X ⟶ Y)
    (f : R →+* S) (c : Sˣ) (a : S)
    (h : d ≫ eY.hom = eX.hom ≫ (projectiveLineScalingIso c).hom ≫
      (projectiveLineTranslationIso a).hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f) :
    Spec.map (CommRingCat.ofHom f) ≫ (projectiveLineSection R ⟨1⟩ ≫ eY.inv) =
      (projectiveLineSection S ⟨1⟩ ≫ eX.inv) ≫ d := by
  apply (cancel_mono eY.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  simp only [Iso.inv_hom_id_assoc]
  exact (infinity_transport f c a).symm

private theorem infinity_structure {R : Type u} [CommRing R] {X : Scheme.{u}}
    (e : X ≅ projectiveScheme R (ULift.{u} (Fin 2))) (π : X ⟶ Spec (.of R))
    (h : π = e.hom ≫ projectiveToSpec R (ULift.{u} (Fin 2))) :
    (projectiveLineSection R ⟨1⟩ ≫ e.inv) ≫ π = 𝟙 _ := by
  rw [h]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using infinity_base (R := R)

private theorem infinity_coordinate {R : Type u} [CommRing R] {X : Scheme.{u}}
    (e : X ≅ projectiveScheme R (ULift.{u} (Fin 2))) :
    (projectiveLineSection R ⟨1⟩ ≫ e.inv) ≫ e.hom = projectiveLineSection R ⟨1⟩ := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- coefficient arrows and affine transitions glue the same infinity section. -/
theorem exists_infinity_diagram {J R : Type u} [Category.{u} J] [CommRing R]
    (N : J ⥤ CommAlgCat.{u} R) (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (e : ∀ j, D.obj j ≅ projectiveScheme (N.obj j.unop) (ULift.{u} (Fin 2)))
    (he : ∀ j, π.app j = (e j).hom ≫
      projectiveToSpec (N.obj j.unop) (ULift.{u} (Fin 2)))
    (c : ∀ {j k : Jᵒᵖ}, (j ⟶ k) → (N.obj j.unop)ˣ)
    (a : ∀ {j k : Jᵒᵖ}, (j ⟶ k) → N.obj j.unop)
    (hmap : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), D.map f ≫ (e k).hom =
      (e j).hom ≫ (projectiveLineScalingIso (c f)).hom ≫
        (projectiveLineTranslationIso (a f)).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f.unop).hom.toRingHom) :
    infinityDiagramSpec N D π e := by
  let s : (N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⟶ D :=
    { app := fun j ↦ projectiveLineSection (N.obj j.unop) ⟨1⟩ ≫ (e j).inv
      naturality := by
        intro j k f
        exact infinity_natural (e j) (e k) (D.map f)
          (N.map f.unop).hom.toRingHom (c f) (a f) (hmap f) }
  refine ⟨s, ?_, ?_⟩
  · apply NatTrans.ext
    funext j
    exact infinity_structure (e j) (π.app j) (he j)
  · intro j
    exact infinity_coordinate (e j)

private theorem colimit_section {C : Type v} [Category.{w} C]
    {J : Type u} [Category.{u} J] (F G : J ⥤ C) (π : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt) (hcomp : ∀ j, cF.ι.app j ≫ q = π.app j ≫ cG.ι.app j)
    (s : G ⟶ F) (hs : s ≫ π = 𝟙 _) :
    ∃ δ : cG.pt ⟶ cF.pt, δ ≫ q = 𝟙 _ ∧
      ∀ j, cG.ι.app j ≫ δ = s.app j ≫ cF.ι.app j := by
  let b := Cocone.mk cF.pt (s ≫ cF.ι)
  let δ := hcG.desc b
  have hδ (j : J) : cG.ι.app j ≫ δ = s.app j ≫ cF.ι.app j := hcG.fac b j
  refine ⟨δ, ?_, hδ⟩
  apply hcG.hom_ext
  intro j
  rw [← Category.assoc, hδ, Category.assoc, hcomp, ← Category.assoc]
  have hsj : s.app j ≫ π.app j = 𝟙 _ := congrArg (fun t ↦ t.app j) hs
  rw [hsj, Category.id_comp, Category.comp_id]

/-- A diagram section induces a closed section on the specified separated bundle colimit. -/
theorem exists_glued_section {J R : Type u} [Category.{u} J] [CommRing R]
    (N : J ⥤ CommAlgCat.{u} R) (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (cD : Cocone D) (q : cD.pt ⟶ cG.pt.left) [IsSeparated q]
    (hcomp : ∀ j, cD.ι.app j ≫ q = π.app j ≫ (cG.ι.app j).left)
    (s : (N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⟶ D)
    (hs : s ≫ π = 𝟙 _) :
    ∃ δ : cG.pt.left ⟶ cD.pt, δ ≫ q = 𝟙 _ ∧ IsClosedImmersion δ ∧
      ∀ j, (cG.ι.app j).left ≫ δ = s.app j ≫ cD.ι.app j := by
  let cB := (Over.forget (Spec (.of R))).mapCocone cG
  have hcB : IsColimit cB := isColimitOfPreserves (Over.forget (Spec (.of R))) hcG
  obtain ⟨δ, hδ, hleg⟩ := colimit_section D
    (N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) π cD cB hcB q hcomp s hs
  have : IsClosedImmersion (δ ≫ q) := by rw [hδ]; infer_instance
  exact ⟨δ, hδ, IsClosedImmersion.of_comp δ q, hleg⟩

end SchubertGeometry
