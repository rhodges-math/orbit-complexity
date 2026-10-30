import OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterPowers
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussPolynomial

/-! # The determinant-power section in the rank-one line -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups TauCeti GroupActions

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The positive frame restricts the fixed coefficient power to the endpoint monomial. -/
theorem positiveDetPower_simple_polynomial (N : ℕ) (i : G.rootBase.support) :
    gaPolynomialEquiv K (G.simpleRootMap i
      (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
        (positiveDetPower G N))) = Polynomial.X ^ (2 * N) := by
  calc
    _ = (gaPolynomialEquiv K (G.simpleRootMap i
        (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
          (positiveDetCoefficient G)))) ^ N := by
      simp only [positiveDetPower, map_pow]
    _ = (Polynomial.X ^ 2) ^ N :=
      congrArg (fun q : Polynomial K => q ^ N) (positiveDet_simple_polynomial G i)
    _ = _ := (pow_mul Polynomial.X 2 N).symm

/-- The negative frame restricts the same coefficient power to one. -/
theorem positiveDetPower_negative_polynomial (N : ℕ) (i : G.rootBase.support) :
    G.negativeSimpleRootMap i (positiveDetPower G N) = 1 := by
  change G.negativeSimpleRootMap i (positiveDetCoefficient G ^ N) = 1
  rw [map_pow, positiveDet_negative_polynomial G i, one_pow]

end SchubertGeometry.DeterminantSection

namespace SchubertGeometry.ProjectiveLine

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def chartCoefficientMap (C : Type u) [CommRing C]
    (j : ULift.{u} (Fin 2)) (q : Polynomial C) :
    (SheafOfModules.unit (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf :
        (projectiveScheme C (ULift.{u} (Fin 2))).Modules) ⟶
      (Scheme.Modules.pushforward (projectiveLinePolynomialChart C j)).obj
        (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit
      (projectiveLinePolynomialChart C j).toRingCatSheafHom ≫
    (Scheme.Modules.pushforward (projectiveLinePolynomialChart C j)).map
      (Scheme.Modules.globalSectionsSmul _ ((Scheme.ΓSpecIso (.of (Polynomial C))).inv q))

private theorem endpoint_projection_left (C : Type u) [CommRing C] (d : ℕ) :
    projectiveAffineEndpoint C d 1 0 ≫
        pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction C)
          (SchubertGeometry.ProjectiveLine.twistedRestriction C d) =
      chartCoefficientMap C ⟨0⟩ (Polynomial.X ^ d) := by
  erw [projectiveAffineEndpoint, pullback.lift_fst]
  change chartCoefficientMap C ⟨0⟩
    ((Polynomial.C 1 * Polynomial.X + Polynomial.C 0) ^ d) = _
  simp only [Polynomial.C_1, one_mul, Polynomial.C_0, add_zero]

private theorem endpoint_projection_right (C : Type u) [CommRing C] (d : ℕ) :
    projectiveAffineEndpoint C d 1 0 ≫
        pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction C)
          (SchubertGeometry.ProjectiveLine.twistedRestriction C d) =
      chartCoefficientMap C ⟨1⟩ 1 := by
  erw [projectiveAffineEndpoint, pullback.lift_snd]
  change chartCoefficientMap C ⟨1⟩
    ((Polynomial.C 1 + Polynomial.C 0 * Polynomial.X) ^ d) = _
  simp only [Polynomial.C_1, Polynomial.C_0, zero_mul, add_zero, one_pow]

private theorem comp_congr_right {C : Type*} [Category C] {A B D : C}
    {f g : A ⟶ B} (h : f = g) (q : B ⟶ D) : f ≫ q = g ≫ q :=
  congrArg (fun f => f ≫ q) h

/-- The normalized global endpoint section for a power of the fixed full character. -/
def determinantEndpoint (N : ℕ) (i : G.rootBase.support) :
    (SheafOfModules.unit (projectiveScheme K (ULift.{u} (Fin 2))).ringCatSheaf :
        (projectiveScheme K (ULift.{u} (Fin 2))).Modules) ⟶
      SchubertGeometry.ProjectiveLine.characterLineModule G i (G.positiveRootCharacter ^ N) :=
  projectiveAffineEndpoint K (2 * N) 1 0 ≫ (SchubertGeometry.ProjectiveLine.characterPowerLineIso G
    N i).inv

/-- The character comparison sends this section to the normalized endpoint. -/
theorem determinantEndpoint_image (N : ℕ) (i : G.rootBase.support) :
    SchubertGeometry.ProjectiveLine.determinantEndpoint G N i ≫
      (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).hom =
      projectiveAffineEndpoint K (2 * N) 1 0 := by
  erw [SchubertGeometry.ProjectiveLine.determinantEndpoint, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The first regular frame coordinate is the pullback of the same determinant power. -/
theorem determinantEndpoint_left (N : ℕ) (i : G.rootBase.support) :
    SchubertGeometry.ProjectiveLine.determinantEndpoint G N i ≫
      (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).hom ≫
        pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction K)
          (SchubertGeometry.ProjectiveLine.twistedRestriction K (2 * N)) =
      SheafOfModules.unitToPushforwardObjUnit
          (projectiveLinePolynomialChart K ⟨0⟩).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (projectiveLinePolynomialChart K ⟨0⟩)).map
          (Scheme.Modules.globalSectionsSmul
            (SheafOfModules.unit (Spec (.of (Polynomial K))).ringCatSheaf)
            ((Scheme.ΓSpecIso (.of (Polynomial K))).inv
              (gaPolynomialEquiv K (G.simpleRootMap i
                (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
                  (DeterminantSection.positiveDetPower G N)))))) := by
  have h := comp_congr_right (SchubertGeometry.ProjectiveLine.determinantEndpoint_image G N i)
    (pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction K)
      (SchubertGeometry.ProjectiveLine.twistedRestriction K (2 * N)))
  have hp := congrArg (chartCoefficientMap K ⟨0⟩)
    (DeterminantSection.positiveDetPower_simple_polynomial G N i)
  exact (Category.assoc (SchubertGeometry.ProjectiveLine.determinantEndpoint G N i)
    (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).hom
    (pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction K)
      (SchubertGeometry.ProjectiveLine.twistedRestriction K (2 * N)))).symm.trans
      (h.trans ((endpoint_projection_left K (2 * N)).trans hp.symm))

/-- The second regular frame coordinate is the pullback of that coefficient to the negative frame.
  -/
theorem determinantEndpoint_right (N : ℕ) (i : G.rootBase.support) :
    SchubertGeometry.ProjectiveLine.determinantEndpoint G N i ≫
      (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).hom ≫
        pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction K)
          (SchubertGeometry.ProjectiveLine.twistedRestriction K (2 * N)) =
      SheafOfModules.unitToPushforwardObjUnit
          (projectiveLinePolynomialChart K ⟨1⟩).toRingCatSheafHom ≫
        (Scheme.Modules.pushforward (projectiveLinePolynomialChart K ⟨1⟩)).map
          (Scheme.Modules.globalSectionsSmul
            (SheafOfModules.unit (Spec (.of (Polynomial K))).ringCatSheaf)
            ((Scheme.ΓSpecIso (.of (Polynomial K))).inv
              (gaPolynomialEquiv K (G.negativeSimpleRootMap i
                (DeterminantSection.positiveDetPower G N))))) := by
  have h := comp_congr_right (SchubertGeometry.ProjectiveLine.determinantEndpoint_image G N i)
    (pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction K)
      (SchubertGeometry.ProjectiveLine.twistedRestriction K (2 * N)))
  have hp : gaPolynomialEquiv K (G.negativeSimpleRootMap i
      (DeterminantSection.positiveDetPower G N)) = 1 := by
    rw [DeterminantSection.positiveDetPower_negative_polynomial, map_one]
  have hm := congrArg (chartCoefficientMap K ⟨1⟩) hp
  exact (Category.assoc (SchubertGeometry.ProjectiveLine.determinantEndpoint G N i)
    (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).hom
    (pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction K)
      (SchubertGeometry.ProjectiveLine.twistedRestriction K (2 * N)))).symm.trans
      (h.trans ((endpoint_projection_right K (2 * N)).trans hm.symm))

end SchubertGeometry.ProjectiveLine
