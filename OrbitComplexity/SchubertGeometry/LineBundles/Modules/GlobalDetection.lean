import OrbitComplexity.SchubertGeometry.LineBundles.Modules.ModuleLocality
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

/-! # Injective Laurent restriction of the projective-line transition module -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory Opposite GroupActions
universe u

private theorem mono_two_right {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (p : B ⟶ D) (q : D ⟶ E)
    (hf : Mono f) (hp : IsIso p) (hq : IsIso q) : Mono (f ≫ p ≫ q) := by
  let : Mono f := hf
  let : IsIso p := hp
  let : IsIso q := hq
  infer_instance

private theorem map_iso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} (f : A ⟶ B) (hf : IsIso f) : IsIso (F.map f) := by
  let : IsIso f := hf
  infer_instance

private theorem mono_iso_right {C : Type*} [Category C]
    {A B D : C} (f : A ⟶ B) (q : B ⟶ D) (hf : Mono f) (hq : IsIso q) :
    Mono (f ≫ q) := by
  let : Mono f := hf
  let : IsIso q := hq
  exact mono_comp _ _

private theorem transitionScalar_isIso (R : Type u) [CommRing R] (d : ℕ) :
    IsIso (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of (LaurentPolynomial R))).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
        (LaurentPolynomial.T (d : ℤ)))) := by
  let z : Γ(Spec (.of (LaurentPolynomial R)), ⊤)ˣ := Units.map
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom
      (unitOfInvertible (LaurentPolynomial.T (R := R) (d : ℤ)))
  change IsIso (Scheme.Modules.globalSectionsSmul _ (z : Γ(Spec (.of (LaurentPolynomial R)), ⊤)))
  exact Scheme.Modules.isIso_globalSectionsSmul_units _ z

private theorem spec_dominant {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) := by
  have hi : Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).injective
    apply hf
    change ((Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom f) a =
      ((Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom f) b
    rw [← Scheme.ΓSpecIso_naturality]
    exact congrArg (Scheme.ΓSpecIso (.of S)).hom hab
  have hz : RingHom.ker (Spec.map (CommRingCat.ofHom f)).appTop.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hi
  constructor
  rw [Scheme.ker_of_isAffine, hz]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp

private abbrev line (R : Type u) [CommRing R] := projectiveScheme R (ULift.{u} (Fin 2))
private abbrev affine (R : Type u) [CommRing R] := Spec (.of (Polynomial R))
private abbrev overlap (R : Type u) [CommRing R] := Spec (.of (LaurentPolynomial R))
private theorem pushforward_unit_mono {X Y Z : Scheme.{u}}
    (j : X ⟶ Y) (r : Z ⟶ X) (hr : IsSchemeTheoreticallyDominant r) (hq : QuasiCompact r) :
    Mono ((Scheme.Modules.pushforward j).map
      (SheafOfModules.unitToPushforwardObjUnit r.toRingCatSheafHom)) := by
  let : IsSchemeTheoreticallyDominant r := hr
  let : QuasiCompact r := hq
  apply (SheafOfModules.forget Y.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  change Function.Injective (r.app (j ⁻¹ᵁ U.unop))
  exact r.app_injective _

private theorem rightRestriction_mono (R : Type u) [CommRing R] :
    Mono (SchubertGeometry.ProjectiveLine.rightRestriction R) := by
  dsimp only [SchubertGeometry.ProjectiveLine.rightRestriction]
  refine mono_two_right _ _ _ (pushforward_unit_mono _ _ ?_ ?_)
    (NatIso.hom_app_isIso _ _) (NatIso.hom_app_isIso _ _)
  · exact spec_dominant _
      ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).injective.comp
        Polynomial.toLaurent_injective)
  · infer_instance

/-- The matching sheaf embeds into the pushforward of its first polynomial chart. -/
def projectiveTransitionEmbed (R : Type u) [CommRing R] (d : ℕ) :
    SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d ⟶
      (Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩)).obj
        (SheafOfModules.unit (affine R).ringCatSheaf) :=
  Limits.pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction R)
    (SchubertGeometry.ProjectiveLine.twistedRestriction R d)

/-- This embedding detects sheaf morphisms without any reducedness assumption on R. -/
theorem projectiveTransitionEmbed_mono (R : Type u) [CommRing R] (d : ℕ) :
    Mono (projectiveTransitionEmbed R d) := by
  let : Mono (SchubertGeometry.ProjectiveLine.twistedRestriction R d) := by
    dsimp only [SchubertGeometry.ProjectiveLine.twistedRestriction]
    apply mono_iso_right _ _ (rightRestriction_mono R)
    exact map_iso _ _ (transitionScalar_isIso R d)
  exact inferInstanceAs (Mono (Limits.pullback.fst
    (SchubertGeometry.ProjectiveLine.leftRestriction R)
      (SchubertGeometry.ProjectiveLine.twistedRestriction R d)))

end SchubertGeometry.ProjectiveLine
