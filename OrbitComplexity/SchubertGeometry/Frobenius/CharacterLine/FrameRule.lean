import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Module
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeScalars
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Function
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeMaps

/-! # Full-character change of regular frames on the flag torsor -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private theorem evaluate_condition {C : Type*} [Category C] {M A B D : C}
    (i : M ⟶ A) (a b : A ⟶ B) (w : B ⟶ B) (t : B ⟶ D)
    (k l : A ⟶ D) (v : D ⟶ D)
    (hc : i ≫ a = i ≫ b ≫ w) (ha : a ≫ t = k) (hb : b ≫ t = l)
    (hw : w ≫ t = t ≫ v) : i ≫ k = i ≫ l ≫ v := by
  rw [← ha, ← hb, ← Category.assoc, hc]
  simp only [Category.assoc, hw]

private def evaluationAdjunct {S : Scheme.{u}} (M : S.Modules) (X : Over S)
    (s : M ⟶ FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X) :
    (Scheme.Modules.pullback X.hom).obj M ⟶
      SheafOfModules.unit X.left.ringCatSheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction X.hom).homEquiv
    M (SheafOfModules.unit X.left.ringCatSheaf)).symm s

private theorem evaluationAdjunct_smul {S : Scheme.{u}} (M : S.Modules) (X : Over S)
    (a b : M ⟶ FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X) (r : Γ(X.left, ⊤))
    (h : a = b ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X r) :
    evaluationAdjunct M X a = evaluationAdjunct M X b ≫
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) r := by
  exact (congrArg (evaluationAdjunct M X) h).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction X.hom).homEquiv_naturality_right_symm
      b (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) r))

private theorem evaluation_covariance {S : Scheme.{u}} (M : S.Modules)
    (Q Z X : Over S) (i : M ⟶ FrobeniusSplitting.CharacterLine.relativeFunctionsObj S Q)
    (r f : Z ⟶ Q) (c : Γ(Z.left, ⊤))
    (hc : i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Z) (Y := Q) r =
      i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Z) (Y := Q) f ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Z c)
    (z : X ⟶ Z) (k l : X ⟶ Q) (hr : z ≫ r = k) (hf : z ≫ f = l) :
    evaluationAdjunct M X (i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y
      := Q) k) =
      evaluationAdjunct M X (i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y
        := Q) l) ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf)
          (z.left.appTop c) := by
  have hr' : FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Z) (Y := Q) r ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Z) z =
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q) k :=
    (CategoryTheory.Functor.map_comp (FrobeniusSplitting.CharacterLine.relativeFunctions S) r.op
      z.op).symm.trans
      (congrArg (fun t => FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q)
        t) hr)
  have hf' : FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Z) (Y := Q) f ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Z) z =
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q) l :=
    (CategoryTheory.Functor.map_comp (FrobeniusSplitting.CharacterLine.relativeFunctions S) f.op
      z.op).symm.trans
      (congrArg (fun t => FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q)
        t) hf)
  have hw : FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Z c ≫
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Z) z =
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Z) z ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X (z.left.appTop c) :=
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul S z c
  have h := evaluate_condition i
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Z) (Y := Q) r)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := Z) (Y := Q) f)
      (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Z c)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Z) z)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q) k)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q) l)
    (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X (z.left.appTop c)) hc hr' hf' hw
  exact evaluationAdjunct_smul M X
    (i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q) k)
    (i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S (X := X) (Y := Q) l) (z.left.appTop
      c) h

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev H := (reductiveVariety G).toOver
private abbrev B := (borelVariety G).toOver
private abbrev F := (flagVariety G).scheme
private abbrev pair := H G ⊗ B G
private abbrev productObj : Over (F G) := Over.mk (flagQuotient G)
private abbrev pairObj : Over (F G) :=
  Over.mk ((fst (H G) (B G)).left ≫ flagQuotient G)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X A : Variety K} [GrpObj A.toOver]
    (f g : X.toOver ⟶ A.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply A.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

private def rightMul : pair G ⟶ H G :=
  fst (H G) (B G) * (snd (H G) (B G) ≫ borelInclusion G)

private theorem right_quotient :
    (rightMul G).left ≫ flagQuotient G = (fst (H G) (B G)).left ≫ flagQuotient G := by
  have h : rightMul G ≫ flagQuotientMorphism G =
      fst (H G) (B G) ≫ flagQuotientMorphism G := by
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
        (Y := reductiveVariety G) (rightMul G) z =
        reductivePointsEquiv G (g * (b : G.points)) := by
      rw [rightMul,
        mapPoints_mul
          (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
          (A := reductiveVariety G),
        Variety.mapPoints_comp
          (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
          (Y := borelVariety G) (Z := reductiveVariety G),
        borelInclusion_points, hg]
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
  exact congrArg (fun f : pair G ⟶ (flagVariety G).toOver => f.left) h

private def rightMap : pairObj G ⟶ productObj G :=
  Over.homMk (rightMul G).left (right_quotient G)

private def firstMap : pairObj G ⟶ productObj G :=
  Over.homMk (fst (H G) (B G)).left rfl

private def weight (chi : G.characters) : Γ((pair G).left, ⊤) :=
  (snd (H G) (B G)).left.appTop (borelCharacterSection G chi)

private def firstRawMap : FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (productObj G)
  ⟶
    FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (pairObj G) :=
  (Scheme.Modules.pushforward (flagQuotient G)).map
      (SheafOfModules.unitToPushforwardObjUnit
        (fst (H G) (B G)).left.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (fst (H G) (B G)).left (flagQuotient G)).hom.app
      (SheafOfModules.unit (pair G).left.ringCatSheaf)

private theorem originalRelativeCondition (chi : G.characters) :
    flagCharacterInclusion G chi ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := pairObj G) (Y :=
          productObj G) (rightMap G) =
      flagCharacterInclusion G chi ≫ firstRawMap G ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (pairObj G) (weight G chi) :=
          by
  have hc : flagCharacterCondition G chi (flagCharacterInclusion G chi) := by
    exact equalizer.condition _ _
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let t : Γ((H G).left, flagQuotient G ⁻¹ᵁ V.unop) :=
    ((flagCharacterInclusion G chi).val.app V).hom s
  have hh := congrArg
    (fun f : flagCharacterModule G chi ⟶ FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G)
      (pairObj G) =>
      (f.val.app V).hom s) hc
  change ((FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := pairObj G) (Y :=
    productObj G)
      (rightMap G)).val.app V).hom t =
    ((FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (pairObj G) (weight G
      chi)).val.app V).hom
      (((firstRawMap G).val.app V).hom t) at hh
  exact hh

private theorem relativeCondition (chi : G.characters) :
    flagCharacterInclusion G chi ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := pairObj G) (Y :=
          productObj G) (rightMap G) =
      flagCharacterInclusion G chi ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := pairObj G) (Y :=
          productObj G) (firstMap G) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (pairObj G) (weight G chi) :=
            by
  have hfirst : FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := pairObj G) (Y :=
    productObj G)
      (firstMap G) = firstRawMap G :=
    FrobeniusSplitting.CharacterLine.relativeFunctionsMap_unit (fst (H G) (B G)).left (flagQuotient
      G)
  exact (originalRelativeCondition G chi).trans
    (congrArg (fun t => flagCharacterInclusion G chi ≫ t ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (F G) (pairObj G) (weight G chi))
        hfirst.symm)

/-- A regular lift of any flag-valued scheme evaluates the pulled-back character module. -/
def characterFrameEvaluation (chi : G.characters)
    (X : Over (Spec (.of K))) (m : X.left ⟶ F G)
    (k : X ⟶ H G) (hk : k.left ≫ flagQuotient G = m) :
    (Scheme.Modules.pullback m).obj (flagCharacterModule G chi) ⟶
      SheafOfModules.unit X.left.ringCatSheaf := by
  let A : Over (F G) := Over.mk m
  let Q : Over (F G) := productObj G
  let f : A ⟶ Q := Over.homMk k.left hk
  let M : (F G).Modules := flagCharacterModule G chi
  let RA : (F G).Modules := FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) A
  let RQ : (F G).Modules := FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) Q
  let i : M ⟶ RQ := flagCharacterInclusion G chi
  let r : RQ ⟶ RA := FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := A) (Y := Q) f
  let s : M ⟶ RA := i ≫ r
  exact evaluationAdjunct (S := F G) (M := M) (X := A) s

/-- Changing the regular frame by its Borel factor multiplies coordinates by the full character. -/
theorem characterFrameEvaluation_rule (chi : G.characters)
    (X : Over (Spec (.of K))) (m : X.left ⟶ F G)
    (k l : X ⟶ H G) (b : X ⟶ B G)
    (hk : k.left ≫ flagQuotient G = m) (hl : l.left ≫ flagQuotient G = m)
    (hkl : k = l * (b ≫ borelInclusion G)) :
    characterFrameEvaluation G chi X m k hk =
      characterFrameEvaluation G chi X m l hl ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf)
          (b.left.appTop (borelCharacterSection G chi)) := by
  let z : X ⟶ pair G := lift l b
  have hz : z.left ≫ (fst (H G) (B G)).left ≫ flagQuotient G = m := by
    have hf : z.left ≫ (fst (H G) (B G)).left = l.left :=
      congrArg (fun f : X ⟶ H G => f.left) (lift_fst l b)
    rw [← Category.assoc, hf, hl]
  let zMap : Over.mk m ⟶ pairObj G := Over.homMk z.left hz
  let kMap : Over.mk m ⟶ productObj G := Over.homMk k.left hk
  let lMap : Over.mk m ⟶ productObj G := Over.homMk l.left hl
  have hkz : zMap ≫ rightMap G = kMap := by
    apply Over.OverMorphism.ext
    change (z ≫ rightMul G).left = k.left
    have he : z ≫ rightMul G = k := by
      dsimp only [z, rightMul]
      rw [MonObj.comp_mul, lift_fst, lift_snd_assoc]
      exact hkl.symm
    exact congrArg (fun f : X ⟶ H G => f.left) he
  have hlz : zMap ≫ firstMap G = lMap := by
    apply Over.OverMorphism.ext
    change (lift l b ≫ fst (H G) (B G)).left = l.left
    rw [lift_fst]
  have hzweight : z.left.appTop (weight G chi) =
      b.left.appTop (borelCharacterSection G chi) := by
    change (z ≫ snd (H G) (B G)).left.appTop (borelCharacterSection G chi) = _
    rw [lift_snd]
  let M : (F G).Modules := flagCharacterModule G chi
  let i : M ⟶ FrobeniusSplitting.CharacterLine.relativeFunctionsObj (F G) (productObj G) :=
    flagCharacterInclusion G chi
  have h := evaluation_covariance (S := F G) (M := M)
    (Q := productObj G) (Z := pairObj G) (X := Over.mk m) (i := i)
    (r := rightMap G) (f := firstMap G) (c := weight G chi)
    (hc := relativeCondition G chi) (z := zMap) (k := kMap) (l := lMap) hkz hlz
  exact h.trans (congrArg (fun c : Γ(X.left, ⊤) =>
    evaluationAdjunct M (Over.mk m)
        (i ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap (F G) (X := Over.mk m) (Y :=
          productObj G) lMap) ≫
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) c)
    hzweight)

end SchubertGeometry.CharacterLine
