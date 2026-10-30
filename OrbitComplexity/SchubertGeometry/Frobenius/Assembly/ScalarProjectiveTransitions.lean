import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarAppendTransitions
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Projective append transitions after scalar extension

The entire projective coordinate change commutes with coefficient extension.
Its two projections identify it on the prescribed scalar model, including
the charts meeting infinity.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchubertGeometry.RetainedCharacter

open private chart_cocone_triangle from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarAppendTransitions
open private coefficient_base from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A (ULift.{u} (Fin 2))

private def affineProjectiveMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) : line B ⟶ line A :=
  (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
    projectiveCoeffMap (ULift.{u} (Fin 2)) f

private theorem projectiveCoeff_square {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (μ : A →+* A') (ν : B →+* B')
    (h : f'.comp μ = ν.comp f) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f' ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) μ =
      projectiveCoeffMap (ULift.{u} (Fin 2)) ν ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f := by
  unfold projectiveCoeffMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.map f' (MvPolynomial.map μ (MvPolynomial.C a)) =
      MvPolynomial.map ν (MvPolynomial.map f (MvPolynomial.C a))
    simp only [MvPolynomial.map_C]
    exact congrArg MvPolynomial.C (RingHom.congr_fun h a)
  · intro i
    change MvPolynomial.map f' (MvPolynomial.map μ (MvPolynomial.X i)) =
      MvPolynomial.map ν (MvPolynomial.map f (MvPolynomial.X i))
    simp only [MvPolynomial.map_X]

private theorem affineProjective_square {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (μ : A →+* A') (ν : B →+* B')
    (h : f'.comp μ = ν.comp f) (a : Bˣ) (b : B) :
    affineProjectiveMap f' (Units.map ν.toMonoidHom a) (ν b) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) μ =
      projectiveCoeffMap (ULift.{u} (Fin 2)) ν ≫ affineProjectiveMap f a b := by
  unfold affineProjectiveMap
  have hc := projectiveCoeff_square f f' μ ν h
  have ha := projectiveAffine_coeff ν a b
  calc
    _ = (projectiveLineScalingIso (Units.map ν.toMonoidHom a)).hom ≫
        (projectiveLineTranslationIso (ν b)).hom ≫
          (projectiveCoeffMap (ULift.{u} (Fin 2)) ν ≫
            projectiveCoeffMap (ULift.{u} (Fin 2)) f) := by
      rw [Category.assoc, Category.assoc, hc]
    _ = ((projectiveLineScalingIso (Units.map ν.toMonoidHom a)).hom ≫
        (projectiveLineTranslationIso (ν b)).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) ν) ≫
            projectiveCoeffMap (ULift.{u} (Fin 2)) f := by simp only [Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f) ha

private theorem affineProjective_scalar {T A B : Type u}
    [CommRing T] [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    (f : A →ₐ[T] B) (a : Bˣ) (b : B) :
    affineProjectiveMap f.toRingHom a b ≫ projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T A)) =
      projectiveToSpec B (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T B)) := by
  have ha : ((projectiveLineScalingIso a).hom ≫
      (projectiveLineTranslationIso b).hom) ≫ projectiveToSpec B (ULift.{u} (Fin 2)) =
      projectiveToSpec B (ULift.{u} (Fin 2)) := by
    rw [Category.assoc, projectiveLineTranslation_base, projectiveLineScaling_base]
  have hc := coefficient_base f.toRingHom
  have hf : f.toRingHom.comp (algebraMap T A) = algebraMap T B := by
    apply RingHom.ext
    exact f.commutes
  calc
    _ = (((projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom) ≫
        (projectiveCoeffMap (ULift.{u} (Fin 2)) f.toRingHom ≫
          projectiveToSpec A (ULift.{u} (Fin 2)))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap T A)) := by
      simp only [affineProjectiveMap, Category.assoc]
    _ = (((projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom) ≫
        (projectiveToSpec B (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom f.toRingHom))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap T A)) :=
      congrArg (fun g => (((projectiveLineScalingIso a).hom ≫
        (projectiveLineTranslationIso b).hom) ≫ g) ≫
          Spec.map (CommRingCat.ofHom (algebraMap T A))) hc
    _ = (projectiveToSpec B (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap T A)) := by rw [← Category.assoc, ha]
    _ = _ := by
      rw [Category.assoc, ← Spec.map_comp]
      exact congrArg (fun g => projectiveToSpec B (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom g)) hf

/-- The original append cocone constructs the entire projective transition
on its prescribed scalar charts from the old and scalar-base projections. -/
theorem scalarAppend_projective_transition {S T : Type u}
    [CommRing S] [CommRing T] [Algebra S T] {J : Type v} [Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S) (M : J ⥤ CommAlgCat.{u} T)
    (μ : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat T) CommRingCat)
    (D : Jᵒᵖ ⥤ Scheme.{u}) (E : ∀ s, D.obj (.op s) ≅ line (N.obj s))
    (c : Cocone D) {s t : J} (f : s ⟶ t) (a : (N.obj t)ˣ) (b : N.obj t)
    (hd : D.map f.op ≫ (E s).hom = (E t).hom ≫
      affineProjectiveMap (N.map f).hom.toRingHom a b)
    (base : c.pt ⟶ Spec (.of S)) {Y : Scheme.{u}}
    (baseT : Y ⟶ Spec (.of T)) (q : Y ⟶ c.pt)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (KA : line (M.obj s) ⟶ Y) (KB : line (M.obj t) ⟶ Y)
    (hAold : KA ≫ q = projectiveCoeffMap (ULift.{u} (Fin 2)) (μ.app s).hom ≫
      (E s).inv ≫ c.ι.app (.op s))
    (hBold : KB ≫ q = projectiveCoeffMap (ULift.{u} (Fin 2)) (μ.app t).hom ≫
      (E t).inv ≫ c.ι.app (.op t))
    (hAbase : KA ≫ baseT = projectiveToSpec (M.obj s) (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T (M.obj s))))
    (hBbase : KB ≫ baseT = projectiveToSpec (M.obj t) (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T (M.obj t)))) :
    affineProjectiveMap (M.map f).hom.toRingHom
      (Units.map (μ.app t).hom.toMonoidHom a) ((μ.app t).hom b) ≫ KA = KB := by
  let g := affineProjectiveMap (N.map f).hom.toRingHom a b
  let g' := affineProjectiveMap (M.map f).hom.toRingHom
    (Units.map (μ.app t).hom.toMonoidHom a) ((μ.app t).hom b)
  have hcoeff : (M.map f).hom.toRingHom.comp (μ.app s).hom =
      (μ.app t).hom.comp (N.map f).hom.toRingHom :=
    congrArg (fun k : CommRingCat.of (N.obj s) ⟶ CommRingCat.of (M.obj t) => k.hom)
      (μ.naturality f).symm
  have hs := affineProjective_square (N.map f).hom.toRingHom (M.map f).hom.toRingHom
    (μ.app s).hom (μ.app t).hom hcoeff a b
  have hold : g ≫ ((E s).inv ≫ c.ι.app (.op s)) = (E t).inv ≫ c.ι.app (.op t) := by
    simpa only [Category.comp_id, Category.id_comp] using
      chart_cocone_triangle (E s) (E t) (D.map f.op) (c.ι.app (.op s))
        (c.ι.app (.op t)) g g (𝟙 _) (𝟙 _) hd (by simp only [Category.comp_id, Category.id_comp])
        (c.w f.op)
  apply hq.hom_ext
  · calc
      _ = g' ≫ (KA ≫ q) := Category.assoc _ _ _
      _ = (g' ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) (μ.app s).hom) ≫
          (E s).inv ≫ c.ι.app (.op s) := by rw [hAold]; simp only [Category.assoc]
      _ = (projectiveCoeffMap (ULift.{u} (Fin 2)) (μ.app t).hom ≫ g) ≫
          (E s).inv ≫ c.ι.app (.op s) :=
        congrArg (fun k => k ≫ (E s).inv ≫ c.ι.app (.op s)) hs
      _ = projectiveCoeffMap (ULift.{u} (Fin 2)) (μ.app t).hom ≫
          (E t).inv ≫ c.ι.app (.op t) := by
        simpa only [Category.assoc] using congrArg
          (fun k => projectiveCoeffMap (ULift.{u} (Fin 2)) (μ.app t).hom ≫ k) hold
      _ = _ := hBold.symm
  · calc
      _ = g' ≫ (KA ≫ baseT) := Category.assoc _ _ _
      _ = g' ≫ projectiveToSpec (M.obj s) (ULift.{u} (Fin 2)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap T (M.obj s))) :=
        congrArg (fun k => g' ≫ k) hAbase
      _ = projectiveToSpec (M.obj t) (ULift.{u} (Fin 2)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap T (M.obj t))) :=
        affineProjective_scalar (M.map f).hom
          (Units.map (μ.app t).hom.toMonoidHom a) ((μ.app t).hom b)
      _ = _ := hBbase.symm

end SchubertGeometry.RetainedCharacter
