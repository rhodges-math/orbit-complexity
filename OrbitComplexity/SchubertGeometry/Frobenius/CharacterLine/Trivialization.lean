import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Module
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Torsor
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.ProductCharts
import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctionMaps
import OrbitComplexity.FrobeniusSplitting.Modules.RestrictionLimits
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeMaps
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # chart trivializations of the full-character sheaf -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private theorem baseChangeNaturality {U Y P₁ P₂ X₁ X₂ : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j]
    (p₁ : P₁ ⟶ U) (p₂ : P₂ ⟶ U) (q₁ : X₁ ⟶ Y) (q₂ : X₂ ⟶ Y)
    (k₁ : P₁ ⟶ X₁) (k₂ : P₂ ⟶ X₂) [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (H₁ : IsPullback p₁ k₁ j q₁) (H₂ : IsPullback p₂ k₂ j q₂)
    (M : Over.mk q₁ ⟶ Over.mk q₂) (N : Over.mk p₁ ⟶ Over.mk p₂)
    (hk : N.left ≫ k₂ = k₁ ≫ M.left) :
    (Scheme.Modules.restrictFunctor j).map
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap Y (X := Over.mk q₁) (Y := Over.mk q₂)
          M) ≫
        (FrobeniusSplitting.CharacterLine.openFunctionsBaseChange p₁ k₁ j q₁ H₁).hom =
      (FrobeniusSplitting.CharacterLine.openFunctionsBaseChange p₂ k₂ j q₂ H₂).hom ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap U (X := Over.mk p₁) (Y := Over.mk p₂)
          N := by
  have h₁ := FrobeniusSplitting.CharacterLine.openFunctionsBaseChange_hom p₁ k₁ j q₁ H₁
  have h₂ := FrobeniusSplitting.CharacterLine.openFunctionsBaseChange_hom p₂ k₂ j q₂ H₂
  exact (congrArg (fun t => (Scheme.Modules.restrictFunctor j).map
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap Y (X := Over.mk q₁) (Y := Over.mk q₂) M)
      ≫ t) h₁).trans
      ((FrobeniusSplitting.CharacterLine.openFunctionsPullback_natural j p₁ p₂ q₁ q₂ k₁ k₂ H₁.w H₂.w
        M N hk).trans
        (congrArg (fun t => t ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsMap U (X := Over.mk p₁) (Y := Over.mk
            p₂) N) h₂.symm))

private theorem baseChangeScalar {U Y P X : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (p : P ⟶ U) (q : X ⟶ Y)
    (k : P ⟶ X) [IsOpenImmersion k] (H : IsPullback p k j q) (r : Γ(X, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul Y
      (Over.mk q) r) ≫
        (FrobeniusSplitting.CharacterLine.openFunctionsBaseChange p k j q H).hom =
      (FrobeniusSplitting.CharacterLine.openFunctionsBaseChange p k j q H).hom ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p) (k.appTop r) := by
  have he := FrobeniusSplitting.CharacterLine.openFunctionsBaseChange_hom p k j q H
  exact (congrArg (fun t => (Scheme.Modules.restrictFunctor j).map
    (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul Y (Over.mk q) r) ≫ t) he).trans
      ((FrobeniusSplitting.CharacterLine.openFunctionsPullback_smul p k j q H.w r).trans
        (congrArg (fun t => t ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p)
          (k.appTop r)) he.symm))

private theorem composeIntertwining {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {A B : C} {A' B' : D} (f : A ⟶ B) (s : B ⟶ B)
    (eA : R.obj A ⟶ A') (eB : R.obj B ⟶ B') (f' : A' ⟶ B') (s' : B' ⟶ B')
    (hf : R.map f ≫ eB = eA ≫ f') (hs : R.map s ≫ eB = eB ≫ s') :
    R.map (f ≫ s) ≫ eB = eA ≫ (f' ≫ s') := by
  rw [Functor.map_comp, Category.assoc, hs, ← Category.assoc, hf, Category.assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev U := (oppositeUnipotentVariety G).toOver
private abbrev B := (borelVariety G).toOver
private abbrev H := (reductiveVariety G).toOver
private abbrev E := U G ⊗ B G
private abbrev Q := E G ⊗ B G
private abbrev F := (flagVariety G).scheme
private abbrev globalProduct : Over (F G) := Over.mk (flagQuotient G)
private abbrev globalPair : Over (F G) :=
  Over.mk ((fst (H G) (B G)).left ≫ flagQuotient G)
private abbrev localProduct : Over (U G).left := Over.mk (fst (U G) (B G)).left
private abbrev localPair : Over (U G).left :=
  Over.mk (fst (E G) (B G) ≫ fst (U G) (B G)).left

private def globalFirst : globalPair G ⟶ globalProduct G :=
  Over.homMk (fst (H G) (B G)).left rfl

private def localFirst : localPair G ⟶ localProduct G :=
  Over.homMk (fst (E G) (B G)).left rfl

private def localMul : localPair G ⟶ localProduct G :=
  Over.homMk (lift (fst (E G) (B G) ≫ fst (U G) (B G))
    ((fst (E G) (B G) ≫ snd (U G) (B G)) * snd (E G) (B G))).left (by
      change (lift _ _ ≫ fst (U G) (B G)).left =
        (fst (E G) (B G) ≫ fst (U G) (B G)).left
      exact congrArg (fun f : Q G ⟶ U G => f.left) (lift_fst _ _))

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X A : Variety K} [GrpObj A.toOver]
    (f g : X.toOver ⟶ A.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply A.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

private theorem rightMul_quotient :
    (fst (H G) (B G) * (snd (H G) (B G) ≫ borelInclusion G)).left ≫
        flagQuotient G = (fst (H G) (B G)).left ≫ flagQuotient G := by
  have ht :
      (fst (H G) (B G) * (snd (H G) (B G) ≫ borelInclusion G)) ≫
          flagQuotientMorphism G = fst (H G) (B G) ≫ flagQuotientMorphism G := by
    apply Variety.mapPoints_injective
      (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
      (Y := flagVariety G)
    funext z
    let g := (reductivePointsMulEquiv G).symm
      (Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (fst (H G) (B G)) z)
    let b := borelPointsMulEquiv G
      (Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := borelVariety G) (snd (H G) (B G)) z)
    have hg : Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (fst (H G) (B G)) z = reductivePointsEquiv G g :=
      ((reductivePointsMulEquiv G).apply_symm_apply _).symm
    have hm : Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G)
        (fst (H G) (B G) * (snd (H G) (B G) ≫ borelInclusion G)) z =
        reductivePointsEquiv G (g * (b : G.points)) := by
      rw [mapPoints_mul
          (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
          (A := reductiveVariety G),
        Variety.mapPoints_comp
          (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
          (Y := borelVariety G) (Z := reductiveVariety G), borelInclusion_points, hg]
      exact ((reductivePointsMulEquiv G).map_mul g (b : G.points)).symm
    rw [Variety.mapPoints_comp
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (Z := flagVariety G),
      Variety.mapPoints_comp
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (Z := flagVariety G), hm, hg,
      flagQuotientMorphism_points, flagQuotientMorphism_points]
    apply congrArg (flagVarietyPointsEquiv G)
    apply (flagProjection_eq_iff G _ _).mpr
    have hb : (g * (b : G.points))⁻¹ * g = (b : G.points)⁻¹ := by group
    rw [hb]
    exact G.borelPoints.inv_mem b.property
  exact congrArg (fun f : H G ⊗ B G ⟶ (flagVariety G).toOver => f.left) ht

private def globalMul : globalPair G ⟶ globalProduct G :=
  Over.homMk
    (fst (H G) (B G) * (snd (H G) (B G) ≫ borelInclusion G)).left (rightMul_quotient G)

private def globalWeight (chi : G.characters) : Γ((globalPair G).left, ⊤) :=
  (snd (H G) (B G)).left.appTop (borelCharacterSection G chi)

private def localWeight (chi : G.characters) : Γ((localPair G).left, ⊤) :=
  (snd (E G) (B G)).left.appTop (borelCharacterSection G chi)

private def productChartIso (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).obj
        (FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (globalProduct G)) ≅
      FrobeniusSplitting.CharacterLine.relativeFunctionsObj (U G).left (localProduct G) :=
  FrobeniusSplitting.CharacterLine.openFunctionsBaseChange (fst (U G) (B G)).left
    (characterTorsorChart G g).left
    (flagChartMorphism G g).left (flagQuotient G)
    ((characterTorsorPullback G g).map (Over.forget (Spec (.of K))))

private def pairChartIso (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).obj
        (FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (globalPair G)) ≅
      FrobeniusSplitting.CharacterLine.relativeFunctionsObj (U G).left (localPair G) :=
  FrobeniusSplitting.CharacterLine.openFunctionsBaseChange (fst (E G) (B G) ≫ fst (U G) (B G)).left
    (characterPairChart G g).left (flagChartMorphism G g).left
    ((fst (H G) (B G)).left ≫ flagQuotient G)
    ((characterPairPullback G g).map (Over.forget (Spec (.of K))))

private theorem first_square (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).map
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (globalFirst G)) ≫
            (pairChartIso G g).hom =
      (productChartIso G g).hom ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left
        (localFirst G) := by
  have hk : (localFirst G).left ≫ (characterTorsorChart G g).left =
      (characterPairChart G g).left ≫ (globalFirst G).left := by
    change (fst (E G) (B G) ≫ characterTorsorChart G g).left =
      (characterPairChart G g ≫ fst (H G) (B G)).left
    exact congrArg (fun f : Q G ⟶ H G => f.left)
      (tensorHom_fst (characterTorsorChart G g) (𝟙 (B G))).symm
  exact baseChangeNaturality (flagChartMorphism G g).left
    (fst (E G) (B G) ≫ fst (U G) (B G)).left (fst (U G) (B G)).left
    ((fst (H G) (B G)).left ≫ flagQuotient G) (flagQuotient G)
    (characterPairChart G g).left (characterTorsorChart G g).left
    ((characterPairPullback G g).map (Over.forget (Spec (.of K))))
    ((characterTorsorPullback G g).map (Over.forget (Spec (.of K))))
    (globalFirst G) (localFirst G) hk

private theorem multiply_square (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).map
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (globalMul G)) ≫
            (pairChartIso G g).hom =
      (productChartIso G g).hom ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left
        (localMul G) := by
  have hk : (localMul G).left ≫ (characterTorsorChart G g).left =
      (characterPairChart G g).left ≫ (globalMul G).left :=
    congrArg (fun f : Q G ⟶ H G => f.left) (characterTorsorChart_mul G g)
  exact baseChangeNaturality (flagChartMorphism G g).left
    (fst (E G) (B G) ≫ fst (U G) (B G)).left (fst (U G) (B G)).left
    ((fst (H G) (B G)).left ≫ flagQuotient G) (flagQuotient G)
    (characterPairChart G g).left (characterTorsorChart G g).left
    ((characterPairPullback G g).map (Over.forget (Spec (.of K))))
    ((characterTorsorPullback G g).map (Over.forget (Spec (.of K))))
    (globalMul G) (localMul G) hk

private theorem weight_chart (g : G.points) (chi : G.characters) :
    (characterPairChart G g).left.appTop (globalWeight G chi) = localWeight G chi := by
  change ((characterPairChart G g ≫ snd (H G) (B G)).left.appTop)
    (borelCharacterSection G chi) = _
  have hs : characterPairChart G g ≫ snd (H G) (B G) = snd (E G) (B G) := by
    rw [characterPairChart, tensorHom_snd, Category.comp_id]
  rw [hs]
  rfl

private theorem weight_square (g : G.points) (chi : G.characters) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).map
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (globalFirst G) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (globalPair G) (globalWeight
            G chi)) ≫
        (pairChartIso G g).hom =
      (productChartIso G g).hom ≫
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (localFirst G) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (localPair G)
            (localWeight G chi)) := by
  have hs : (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).map
        (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (globalPair G) (globalWeight G
          chi)) ≫
        (pairChartIso G g).hom =
      (pairChartIso G g).hom ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (localPair G) (localWeight
          G chi) := by
    have h := baseChangeScalar (flagChartMorphism G g).left
      (fst (E G) (B G) ≫ fst (U G) (B G)).left
      ((fst (H G) (B G)).left ≫ flagQuotient G) (characterPairChart G g).left
      ((characterPairPullback G g).map (Over.forget (Spec (.of K)))) (globalWeight G chi)
    exact h.trans (congrArg (fun r => (pairChartIso G g).hom ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (localPair G) r)
        (weight_chart G g chi))
  exact composeIntertwining (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (globalFirst G))
    (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (globalPair G) (globalWeight G
      chi))
    (productChartIso G g).hom (pairChartIso G g).hom
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (localFirst G))
    (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (localPair G) (localWeight G
      chi))
    (first_square G g) hs

/-- The full-character sheaf is the structure module on each original flag-torsor chart. -/
def flagCharacterChartIso (g : G.points) (chi : G.characters) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).obj
        (flagCharacterModule G chi) ≅ SheafOfModules.unit (U G).left.ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor (flagChartMorphism G g).left
  let : PreservesLimitsOfSize.{u, u} R :=
    FrobeniusSplitting.RetainedCharacter.restrictPreservesLimits (flagChartMorphism G g).left
  let rawFirst : FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (globalProduct G) ⟶
      FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (globalPair G) :=
    (Scheme.Modules.pushforward (flagQuotient G)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (fst (H G) (B G)).left.toRingCatSheafHom) ≫
      (Scheme.Modules.pushforwardComp (fst (H G) (B G)).left (flagQuotient G)).hom.app
        (SheafOfModules.unit (H G ⊗ B G).left.ringCatSheaf)
  have hfirst : FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := globalPair G) (Y
    := globalProduct G)
      (globalFirst G) = rawFirst :=
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap_unit (fst (H G) (B G)).left (flagQuotient
      G)
  let a := FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := globalPair G) (Y :=
    globalProduct G) (globalMul G)
  let b := rawFirst ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (globalPair G)
    (globalWeight G chi)
  have hb : b = FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := globalPair G) (Y
    := globalProduct G)
      (globalFirst G) ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (globalPair G)
        (globalWeight G chi) :=
    congrArg (fun t => t ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (globalPair G) (globalWeight G
        chi)) hfirst.symm
  have hw : R.map b ≫ (pairChartIso G g).hom =
      (productChartIso G g).hom ≫
        (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (localFirst G) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (localPair G)
            (localWeight G chi)) :=
    (congrArg (fun t => R.map t ≫ (pairChartIso G g).hom) hb).trans (weight_square G g chi)
  change R.obj (equalizer a b) ≅ _
  refine PreservesEqualizer.iso R a b ≪≫
    HasLimit.isoOfNatIso (parallelPairIso (R.map a) (R.map b)
      (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (localMul G))
      (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (localFirst G) ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (localPair G) (localWeight
          G chi))
      (productChartIso G g) (pairChartIso G g) (multiply_square G g) hw) ≪≫ ?_
  exact (localCharacterIso G chi).symm

end SchubertGeometry.CharacterLine
