import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficients of open-range frame factors

The coordinate isomorphism through the open subscheme agrees with transport
from the image of the top open. The comparison is proved over arbitrary open
immersions and whole ring maps before evaluating any retained coefficient.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveCartier

open private rangeScalar image_top_range
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
open private chartCoordinateIso retainedCoordinateIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
open private originalLeg originalLegOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames

private def rangeScalarHom {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Γ(X, ⊤) ⟶ Γ(Y, j.opensRange) :=
  (j.appIso ⊤).inv ≫ Y.presheaf.map (eqToHom (image_top_range j).symm).op

private def rangeCoordinateIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Γ(Y, j.opensRange) ≅ Γ(X, ⊤) :=
  j.opensRange.topIso.symm ≪≫ Scheme.Γ.mapIso j.isoOpensRange.op

private theorem top_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  change f.appTop ≫ X.presheaf.map (homOfLE h).op = f.appTop
  have hi : (homOfLE h).op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem inclusion_appLE {Y : Scheme.{u}} (U : Y.Opens)
    (h : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) :
    U.ι.appLE U ⊤ h = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  change Y.presheaf.map _ = Y.presheaf.map _
  exact congrArg Y.presheaf.map (Subsingleton.elim _ _)

private theorem rangeCoordinate_appLE {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (h : (⊤ : X.Opens) ≤ j ⁻¹ᵁ j.opensRange) :
    (rangeCoordinateIso j).hom = j.appLE j.opensRange ⊤ h := by
  let U := j.opensRange
  let r := j.isoOpensRange.hom
  have hU : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have hX : (⊤ : X.Opens) ≤ r ⁻¹ᵁ (⊤ : U.toScheme.Opens) := by simp
  have hr : r ≫ U.ι = j := j.isoOpensRange_hom_ι
  have hc : U.ι.appLE U ⊤ hU ≫ r.appLE ⊤ ⊤ hX = j.appLE U ⊤ h := by
    simpa only [hr] using Scheme.Hom.appLE_comp_appLE r U.ι U ⊤ ⊤ hU hX
  calc
    _ = U.topIso.inv ≫ r.appTop := rfl
    _ = U.ι.appLE U ⊤ hU ≫ r.appLE ⊤ ⊤ hX :=
      congrArg₂ (fun a b => a ≫ b) (inclusion_appLE U hU).symm (top_appLE r hX).symm
    _ = _ := hc

private theorem presheaf_equality_loop {X : Scheme.{u}}
    (F : X.Opensᵒᵖ ⥤ CommRingCat.{u}) {U V : X.Opens} (h : U = V) :
    F.map (eqToHom h).op ≫ F.map (eqToHom h.symm).op = 𝟙 (F.obj (op V)) := by
  rw [← CategoryTheory.Functor.map_comp]
  have hi : (eqToHom h).op ≫ (eqToHom h.symm).op = 𝟙 (op V) := Subsingleton.elim _ _
  rw [hi, CategoryTheory.Functor.map_id]

private theorem rangeCoordinate_retraction {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (rangeCoordinateIso j).hom ≫ rangeScalarHom j =
      𝟙 (Γ(Y, j.opensRange)) := by
  have hpre : (⊤ : X.Opens) ≤ j ⁻¹ᵁ j.opensRange := by simp
  have hα := rangeCoordinate_appLE j hpre
  have hj : j.appLE j.opensRange ⊤ hpre ≫ (j.appIso ⊤).inv =
      Y.presheaf.map (eqToHom (image_top_range j)).op := by
    refine (j.appLE_appIso_inv hpre).trans ?_
    exact congrArg Y.presheaf.map (Subsingleton.elim _ _)
  calc
    _ = (j.appLE j.opensRange ⊤ hpre ≫ (j.appIso ⊤).inv) ≫
        Y.presheaf.map (eqToHom (image_top_range j).symm).op := by
      rw [hα]
      exact (Category.assoc _ _ _).symm
    _ = Y.presheaf.map (eqToHom (image_top_range j)).op ≫
        Y.presheaf.map (eqToHom (image_top_range j).symm).op :=
      congrArg (fun a => a ≫ Y.presheaf.map (eqToHom (image_top_range j).symm).op) hj
    _ = _ := presheaf_equality_loop Y.presheaf (image_top_range j)

private theorem iso_retraction {C : Type v} [Category.{w} C]
    {A B D : C} (E : A ≅ B) (S : B ≅ D) (v : B ⟶ A)
    (h : E.hom ≫ v = 𝟙 A) : S.inv ≫ v ≫ E.hom ≫ S.hom = 𝟙 D := by
  have hv : v = E.inv := by
    apply (cancel_epi E.hom).mp
    exact h.trans E.hom_inv_id.symm
  rw [hv]
  simp only [E.inv_hom_id_assoc, S.inv_hom_id]

/-- The coordinate map of an arbitrary affine open immersion recovers a
coefficient transported through its open range. -/
theorem chartCoordinate_rangeScalar {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j] (x : A) :
    (chartCoordinateIso j).hom (rangeScalar j ((Scheme.ΓSpecIso (.of A)).inv x)) = x := by
  have h := iso_retraction (rangeCoordinateIso j) (Scheme.ΓSpecIso (.of A))
    (rangeScalarHom j) (rangeCoordinate_retraction j)
  exact ConcreteCategory.congr_hom h x

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)

/-- The retained prior-frame factor has exactly the inverse adjusted
character-power coefficient in the unchanged overlap ring. -/
theorem retainedFrameFactor_coefficient (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ) :
    (retainedCoordinateIso N cN hcN s).hom
        (RetainedCharacter.retainedMatchingFrameFactor N cN hcN delta n s j hj k hk d e) =
      ((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s) :=
  @chartCoordinate_rangeScalar (N.obj s) _ cN.pt.left
    (originalLeg N cN s) (originalLegOpen N cN hcN s)
    ((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s)

end SchubertGeometry.ProjectiveCartier
