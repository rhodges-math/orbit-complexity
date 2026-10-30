import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

/-! # The affine transform of the endpoint monomial -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveLine
open SchubertGeometry.ProjectiveLine

private def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private abbrev line (C : Type u) [CommRing C] := projectiveScheme C (ULift.{u} (Fin 2))
private abbrev affine (C : Type u) [CommRing C] := Spec (.of (Polynomial C))
private abbrev overlap (C : Type u) [CommRing C] := Spec (.of (LaurentPolynomial C))
private abbrev chart (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  projectiveLinePolynomialChart C j

private def leftMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

private def rightMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

private def overlapMap (C : Type u) [CommRing C] : overlap C ⟶ line C :=
  leftMap C ≫ chart C ⟨0⟩

private def chartModule (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    (line C).Modules :=
  (Scheme.Modules.pushforward (chart C j)).obj (SheafOfModules.unit (affine C).ringCatSheaf)

private def transitionSection (C : Type u) [CommRing C] (d : ℕ) : Γ(overlap C, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv (LaurentPolynomial.T (d : ℤ))

private abbrev chartCounit (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso (chart C j)).app
    (structureModule (affine C))).hom

private theorem unit_top_ext {X : Scheme.{u}} {M : X.Modules}
    (f g : structureModule X ⟶ M)
    (h : (f.val.app (.op ⊤)).hom (1 : Γ(X, ⊤)) =
      (g.val.app (.op ⊤)).hom (1 : Γ(X, ⊤))) : f = g := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hf := PresheafOfModules.sections_property (M.unitHomEquiv f) U.unop.leTop.op
  have hg := PresheafOfModules.sections_property (M.unitHomEquiv g) U.unop.leTop.op
  rw [← hf, ← hg]
  exact congrArg (M.val.map U.unop.leTop.op) h

private def chartSection (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2))
    (f : Polynomial C) : structureModule (line C) ⟶ chartModule C j :=
  SheafOfModules.unitToPushforwardObjUnit (chart C j).toRingCatSheafHom ≫
    (Scheme.Modules.pushforward (chart C j)).map
      (Scheme.Modules.globalSectionsSmul _ ((Scheme.ΓSpecIso (.of (Polynomial C))).inv f))

private theorem module_comp_apply {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : X.Opens) (s : M.val.obj (.op U)) :
    ((f ≫ g).val.app (.op U)).hom s =
      (g.val.app (.op U)).hom ((f.val.app (.op U)).hom s) := rfl

private theorem chartSection_top (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2))
    (f : Polynomial C) :
    ((chartSection C j f).val.app (.op ⊤)).hom (1 : Γ(line C, ⊤)) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv f := by
  change (affine C).presheaf.map (𝟙 (.op ⊤))
      ((Scheme.ΓSpecIso (.of (Polynomial C))).inv f) * (chart C j).appTop 1 = _
  simp

private theorem leftRestriction_top (C : Type u) [CommRing C] (s : Γ(affine C, ⊤)) :
    ((SchubertGeometry.ProjectiveLine.leftRestriction C).val.app (.op ⊤)).hom s = (leftMap C).appTop
      s := rfl

private theorem rightRestriction_top (C : Type u) [CommRing C] (s : Γ(affine C, ⊤)) :
    ((SchubertGeometry.ProjectiveLine.rightRestriction C).val.app (.op ⊤)).hom s = (rightMap
      C).appTop s := by
  change (overlap C).presheaf.map (𝟙 (.op ⊤)) ((rightMap C).appTop s) = _
  simp

private theorem twistedRestriction_top (C : Type u) [CommRing C] (d : ℕ)
    (s : Γ(affine C, ⊤)) :
    ((SchubertGeometry.ProjectiveLine.twistedRestriction C d).val.app (.op ⊤)).hom s =
      transitionSection C d * (rightMap C).appTop s := by
  erw [module_comp_apply (SchubertGeometry.ProjectiveLine.rightRestriction C)
    ((Scheme.Modules.pushforward (overlapMap C)).map
      (Scheme.Modules.globalSectionsSmul _ (transitionSection C d))) ⊤ s,
    rightRestriction_top C s]
  change (overlap C).presheaf.map (𝟙 (.op ⊤)) (transitionSection C d) *
    (rightMap C).appTop s = _
  simp

private theorem affine_values (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    (leftMap R).appTop ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
        ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d)) =
      transitionSection R d * (rightMap R).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
          ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d)) := by
  let f : Polynomial R := (Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d
  let g : Polynomial R := (Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d
  have h0 := congrArg (fun q => q f) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)))
  have h1 := congrArg (fun q => q g) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom.comp
        Polynomial.toLaurent)))
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (Polynomial.toLaurent f) =
    (leftMap R).appTop ((Scheme.ΓSpecIso (.of (Polynomial R))).inv f) at h0
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
      (LaurentPolynomial.invert (Polynomial.toLaurent g)) =
    (rightMap R).appTop ((Scheme.ΓSpecIso (.of (Polynomial R))).inv g) at h1
  rw [← h0, ← h1]
  change _ = (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
      (LaurentPolynomial.T (d : ℤ)) * _
  rw [← map_mul]
  apply congrArg (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
  have hT : LaurentPolynomial.T (R := R) (d : ℤ) =
      (LaurentPolynomial.T (R := R) 1) ^ d := by
    simpa only [map_pow, Polynomial.toLaurent_X] using
      (Polynomial.toLaurent_X_pow (R := R) d).symm
  rw [hT]
  dsimp only [f, g]
  simp only [map_pow, map_add, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  rw [← mul_pow]
  congr 1
  have hu : LaurentPolynomial.T (R := R) 1 * LaurentPolynomial.T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  calc
    _ = LaurentPolynomial.C c * LaurentPolynomial.T 1 +
        LaurentPolynomial.C b * (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by
      rw [hu, mul_one]
    _ = _ := by ring

private theorem affine_matching (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    chartSection R ⟨0⟩ ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d) ≫
        SchubertGeometry.ProjectiveLine.leftRestriction R =
      chartSection R ⟨1⟩ ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d) ≫
        SchubertGeometry.ProjectiveLine.twistedRestriction R d := by
  apply unit_top_ext
  have hleft :
      ((chartSection R ⟨0⟩ ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d) ≫
          SchubertGeometry.ProjectiveLine.leftRestriction R).val.app (.op ⊤)).hom (1 : Γ(line R, ⊤))
            =
        (leftMap R).appTop ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
          ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d)) :=
    (module_comp_apply
      (chartSection R ⟨0⟩ ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d))
      (SchubertGeometry.ProjectiveLine.leftRestriction R) ⊤ (1 : Γ(line R, ⊤))).trans
      ((congrArg (fun s : Γ(affine R, ⊤) =>
        ((SchubertGeometry.ProjectiveLine.leftRestriction R).val.app (.op ⊤)).hom s)
          (chartSection_top R ⟨0⟩ _)).trans (leftRestriction_top R _))
  have hright :
      ((chartSection R ⟨1⟩ ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d) ≫
          SchubertGeometry.ProjectiveLine.twistedRestriction R d).val.app (.op ⊤)).hom (1 : Γ(line
            R, ⊤)) =
        transitionSection R d * (rightMap R).appTop
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv
            ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d)) :=
    (module_comp_apply
      (chartSection R ⟨1⟩ ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d))
      (SchubertGeometry.ProjectiveLine.twistedRestriction R d) ⊤ (1 : Γ(line R, ⊤))).trans
      ((congrArg (fun s : Γ(affine R, ⊤) =>
        ((SchubertGeometry.ProjectiveLine.twistedRestriction R d).val.app (.op ⊤)).hom s)
          (chartSection_top R ⟨1⟩ _)).trans (twistedRestriction_top R d _))
  exact hleft.trans ((affine_values R d c b).trans hright.symm)

private def endpointLeft (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    structureModule (line R) ⟶ chartModule R ⟨0⟩ :=
  chartSection R ⟨0⟩ ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d)

private def endpointRight (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    structureModule (line R) ⟶ chartModule R ⟨1⟩ :=
  chartSection R ⟨1⟩ ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d)

private theorem endpoint_matching (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    endpointLeft R d c b ≫ SchubertGeometry.ProjectiveLine.leftRestriction R =
      endpointRight R d c b ≫ SchubertGeometry.ProjectiveLine.twistedRestriction R d :=
  affine_matching R d c b

private theorem endpoint_hasPullback (R : Type u) [CommRing R] (d : ℕ) :
    HasPullback (SchubertGeometry.ProjectiveLine.leftRestriction R)
      (SchubertGeometry.ProjectiveLine.twistedRestriction R d) := by
  let : HasFiniteLimits ((line R).Modules) :=
    SheafOfModules.Finite.hasFiniteLimits (line R).ringCatSheaf
  let : HasLimitsOfShape WalkingCospan ((line R).Modules) :=
    HasFiniteLimits.out WalkingCospan
  exact HasLimitsOfShape.has_limit
    (cospan (SchubertGeometry.ProjectiveLine.leftRestriction R)
      (SchubertGeometry.ProjectiveLine.twistedRestriction R d))

private def matchingPullbackLift {D : Type v} [Category.{w} D]
    {W X Y Z : D} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (hm : h ≫ f = k ≫ g) :
    W ⟶ pullback f g :=
  pullback.lift h k hm

private def endpointLift (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    structureModule (line R) ⟶
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d := by
  letI : HasPullback (SchubertGeometry.ProjectiveLine.leftRestriction R)
      (SchubertGeometry.ProjectiveLine.twistedRestriction R d) :=
    endpoint_hasPullback R d
  exact matchingPullbackLift (D := (line R).Modules)
    (SchubertGeometry.ProjectiveLine.leftRestriction R)
    (SchubertGeometry.ProjectiveLine.twistedRestriction R d)
    (endpointLeft R d c b) (endpointRight R d c b) (endpoint_matching R d c b)

/-- The affine transform of X^d is a global section with its two regular coordinates. -/
def projectiveAffineEndpoint (R : Type u) [CommRing R] (d : ℕ) (c b : R) :
    structureModule (line R) ⟶ SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d :=
  endpointLift R d c b

end SchubertGeometry.ProjectiveLine
