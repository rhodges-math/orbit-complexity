import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-! # Scalar compatibility for the infinity factor -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

private theorem unitRestriction_smul {A B : Scheme.{u}} (f : A ⟶ B)
    (r : Γ(B, ⊤)) :
    Scheme.Modules.globalSectionsSmul (SheafOfModules.unit B.ringCatSheaf) r ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit A.ringCatSheaf)
            (f.appTop r)) := by
  erw [Scheme.Modules.pushforward_map_globalSectionsSmul]
  exact Scheme.Modules.globalSectionsSmul_naturality
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) r

private theorem compositeRestriction_smul {A B X : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ X) (h : A ⟶ X) (hf : f ≫ g = h)
    (r : Γ(B, ⊤)) (s : Γ(A, ⊤)) :
    (Scheme.Modules.pushforward g).map
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit B.ringCatSheaf) r) ≫
      ((Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          (SheafOfModules.unit A.ringCatSheaf) ≫
        (Scheme.Modules.pushforwardCongr hf).hom.app
          (SheafOfModules.unit A.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward h).map
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit A.ringCatSheaf) s) =
    ((Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          (SheafOfModules.unit A.ringCatSheaf) ≫
        (Scheme.Modules.pushforwardCongr hf).hom.app
          (SheafOfModules.unit A.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward h).map
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit A.ringCatSheaf)
          (s * f.appTop r)) := by
  let F := Scheme.Modules.pushforward g
  let G := Scheme.Modules.pushforward h
  let Q := (Scheme.Modules.pushforwardComp f g) ≪≫
    Scheme.Modules.pushforwardCongr hf
  let M : A.Modules := SheafOfModules.unit A.ringCatSheaf
  let N : B.Modules := SheafOfModules.unit B.ringCatSheaf
  let v : N ⟶ (Scheme.Modules.pushforward f).obj M :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let a := Scheme.Modules.globalSectionsSmul N r
  let b := Scheme.Modules.globalSectionsSmul M (f.appTop r)
  let c := Scheme.Modules.globalSectionsSmul M s
  change F.map a ≫ (F.map v ≫ Q.hom.app M) ≫ G.map c =
    (F.map v ≫ Q.hom.app M) ≫ G.map
      (Scheme.Modules.globalSectionsSmul M (s * f.appTop r))
  have hv : a ≫ v = v ≫ (Scheme.Modules.pushforward f).map b :=
    unitRestriction_smul f r
  calc
    F.map a ≫ (F.map v ≫ Q.hom.app M) ≫ G.map c =
        F.map (a ≫ v) ≫ Q.hom.app M ≫ G.map c := by
          erw [Functor.map_comp]
          simp only [Category.assoc]
    _ = F.map (v ≫ (Scheme.Modules.pushforward f).map b) ≫
        Q.hom.app M ≫ G.map c := by erw [hv]
    _ = F.map v ≫ Q.hom.app M ≫ G.map b ≫ G.map c := by
      erw [Functor.map_comp]
      simp only [Category.assoc]
      erw [Q.hom.naturality_assoc]
    _ = (F.map v ≫ Q.hom.app M) ≫ G.map
        (Scheme.Modules.globalSectionsSmul M (s * f.appTop r)) := by
      erw [Scheme.Modules.globalSectionsSmul_mul, Functor.map_comp]
      simp only [Category.assoc]
      rfl

open GroupActions SchubertGeometry.ProjectiveLine

private abbrev line (C : Type u) [CommRing C] := projectiveScheme C (ULift.{u} (Fin 2))
private abbrev affine (C : Type u) [CommRing C] := Spec (.of (Polynomial C))
private abbrev overlap (C : Type u) [CommRing C] := Spec (.of (LaurentPolynomial C))
private abbrev chart (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  projectiveLinePolynomialChart C j

private def rightMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

private def overlapMap (C : Type u) [CommRing C] : overlap C ⟶ line C :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫ chart C ⟨0⟩

private def transition (C : Type u) [CommRing C] (d : ℕ) : Γ(overlap C, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv (LaurentPolynomial.T (d : ℤ))

private def polynomialPower (C : Type u) [CommRing C] (d : ℕ) : Γ(affine C, ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ d)

private def chart1Multiply (C : Type u) [CommRing C] (d : ℕ) :=
  (Scheme.Modules.pushforward (chart C ⟨1⟩)).map
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (affine C).ringCatSheaf)
      (polynomialPower C d))

private def reciprocalRestriction (C : Type u) [CommRing C] :
    (Scheme.Modules.pushforward (chart C ⟨1⟩)).obj
        (SheafOfModules.unit (affine C).ringCatSheaf) ⟶
      (Scheme.Modules.pushforward (overlapMap C)).obj
        (SheafOfModules.unit (overlap C).ringCatSheaf) :=
  (Scheme.Modules.pushforward (chart C ⟨1⟩)).map
      (SheafOfModules.unitToPushforwardObjUnit (rightMap C).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (rightMap C) (chart C ⟨1⟩)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (projectiveLinePolynomial_overlap C).symm).hom.app _

private theorem reciprocalRestriction_eq (C : Type u) [CommRing C] :
    reciprocalRestriction C = rightRestriction C := by
  rfl

private theorem infinity_matching (C : Type u) [CommRing C] (d : ℕ) :
    transition C (2 * d) * (rightMap C).appTop (polynomialPower C d) =
      transition C d := by
  have h := congrArg (fun f => f (Polynomial.X ^ d))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C] LaurentPolynomial C).toRingHom.comp
        Polynomial.toLaurent)))
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv
    (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X ^ d))) =
      (rightMap C).appTop (polynomialPower C d) at h
  rw [← h]
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv (LaurentPolynomial.T _) *
      (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv
        (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X ^ d))) = _
  have he : LaurentPolynomial.T (R := C) ((2 * d : ℕ) : ℤ) *
      LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X ^ d)) =
        LaurentPolynomial.T (d : ℤ) := by
    simp only [Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_T]
    rw [← LaurentPolynomial.T_add]
    congr 1
    omega
  exact (map_mul (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv.hom _ _).symm.trans
    (congrArg ((Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv) he)

private theorem chart1Multiply_matching (C : Type u) [CommRing C] (d : ℕ) :
    chart1Multiply C d ≫ twistedRestriction C (2 * d) = twistedRestriction C d := by
  have h := compositeRestriction_smul (rightMap C) (chart C ⟨1⟩) (overlapMap C)
    (projectiveLinePolynomial_overlap C).symm (polynomialPower C d) (transition C (2 * d))
  rw [infinity_matching C d] at h
  change chart1Multiply C d ≫ (reciprocalRestriction C ≫
      (Scheme.Modules.pushforward (overlapMap C)).map
        (Scheme.Modules.globalSectionsSmul
          (SheafOfModules.unit (overlap C).ringCatSheaf) (transition C (2 * d)))) =
    reciprocalRestriction C ≫ (Scheme.Modules.pushforward (overlapMap C)).map
      (Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (overlap C).ringCatSheaf) (transition C d)) at h
  erw [reciprocalRestriction_eq C] at h
  exact h

/-- Multiplication by the infinity factor has chart values one and Y^d. -/
def projectiveInfinityFactor (C : Type u) [CommRing C] (d : ℕ) :
    projectiveTransitionModule C d ⟶ projectiveTransitionModule C (2 * d) :=
  pullback.lift (pullback.fst (leftRestriction C) (twistedRestriction C d))
    (pullback.snd (leftRestriction C) (twistedRestriction C d) ≫ chart1Multiply C d)
    (by erw [Category.assoc, chart1Multiply_matching]; exact pullback.condition)

private theorem infinity_fst (C : Type u) [CommRing C] (d : ℕ) :
    projectiveInfinityFactor C d ≫
        pullback.fst (leftRestriction C) (twistedRestriction C (2 * d)) =
      pullback.fst (leftRestriction C) (twistedRestriction C d) :=
  pullback.lift_fst _ _ _

private theorem infinity_snd (C : Type u) [CommRing C] (d : ℕ) :
    projectiveInfinityFactor C d ≫
        pullback.snd (leftRestriction C) (twistedRestriction C (2 * d)) =
      pullback.snd (leftRestriction C) (twistedRestriction C d) ≫ chart1Multiply C d :=
  pullback.lift_snd _ _ _

private theorem infinity_left (C : Type u) [CommRing C] (d : ℕ) :
    (Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).map (projectiveInfinityFactor C d) ≫
        leftChartMap C (2 * d) = leftChartMap C d := by
  dsimp only [leftChartMap]
  erw [← Category.assoc, ← Functor.map_comp, infinity_fst]

private theorem infinity_right (C : Type u) [CommRing C] (d : ℕ) :
    (Scheme.Modules.restrictFunctor (chart C ⟨1⟩)).map (projectiveInfinityFactor C d) ≫
        rightChartMap C (2 * d) = rightChartMap C d ≫
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (affine C).ringCatSheaf)
        (polynomialPower C d) := by
  let M : (affine C).Modules := SheafOfModules.unit (affine C).ringCatSheaf
  let s := Scheme.Modules.globalSectionsSmul M (polynomialPower C d)
  let F := Scheme.Modules.restrictFunctor (chart C ⟨1⟩)
  let ε := (Scheme.Modules.restrictFunctorAdjCounitIso (chart C ⟨1⟩)).hom
  change F.map (projectiveInfinityFactor C d) ≫
      (F.map (pullback.snd (leftRestriction C) (twistedRestriction C (2 * d))) ≫
        ε.app M) =
    (F.map (pullback.snd (leftRestriction C) (twistedRestriction C d)) ≫ ε.app M) ≫ s
  erw [← Category.assoc, ← F.map_comp, infinity_snd, F.map_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t =>
      F.map (pullback.snd (leftRestriction C) (twistedRestriction C d)) ≫ t)
        (ε.naturality s)).trans (Category.assoc _ _ _).symm)

/-- The infinity-factor map is the identity on the first chart and multiplication
by the specified coordinate power on the reciprocal chart. -/
theorem projectiveInfinityFactor_charts (C : Type u) [CommRing C] (d : ℕ) :
    ((Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart C ⟨0⟩)).map
        (projectiveInfinityFactor C d) ≫ leftChartMap C (2 * d) = leftChartMap C d) ∧
    ((Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart C ⟨1⟩)).map
        (projectiveInfinityFactor C d) ≫ rightChartMap C (2 * d) =
      rightChartMap C d ≫ Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ d))) :=
  ⟨infinity_left C d, infinity_right C d⟩

end SchubertGeometry.ProjectiveLine
