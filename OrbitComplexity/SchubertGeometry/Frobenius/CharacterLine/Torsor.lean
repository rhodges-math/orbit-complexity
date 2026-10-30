import OrbitComplexity.FrobeniusSplitting.Modules.IdentityCharacter
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Function
import OrbitComplexity.GroupActions.Varieties.OppositeUnipotentVariety
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # The character module on the trivial Borel torsor -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private theorem identityIso_inclusion {S : Scheme.{u}} {A X Q : Over S}
    (m f : Q ⟶ X) (i : X ⟶ Q) (p : X ⟶ A) (s : A ⟶ X)
    (c : Γ(X.left, ⊤)) (v : Γ(Q.left, ⊤))
    (him : i ≫ m = 𝟙 X) (hif : i ≫ f = p ≫ s) (hsp : s ≫ p = 𝟙 A)
    (hbase : m ≫ p = f ≫ p) (hvi : i.left.appTop v = c)
    (hcs : s.left.appTop c = 1) (hcm : m.left.appTop c = f.left.appTop c * v) :
    (FrobeniusSplitting.CharacterLine.identityCharacterIso S m f i p s c v him hif hsp hbase hvi hcs
      hcm).hom ≫
        equalizer.ι (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S m)
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Q v) =
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S p ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X c := by
  change equalizer.lift _ _ ≫ equalizer.ι _ _ = _
  exact equalizer.lift_ι _ _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev U := (oppositeUnipotentVariety G).toOver
private abbrev B := (borelVariety G).toOver
private abbrev E := U G ⊗ B G
private abbrev Q := E G ⊗ B G

private def projection : E G ⟶ U G := fst _ _
private def first : Q G ⟶ E G := fst _ _
private def unitFrame : U G ⟶ E G := lift (𝟙 (U G)) 1
private def multiply : Q G ⟶ E G :=
  lift (first G ≫ projection G)
    ((first G ≫ snd (U G) (B G)) * snd (E G) (B G))
private def insert : E G ⟶ Q G :=
  lift (projection G ≫ unitFrame G) (snd (U G) (B G))

private theorem section_projection : unitFrame G ≫ projection G = 𝟙 (U G) :=
  lift_fst _ _

private theorem multiply_projection :
    multiply G ≫ projection G = first G ≫ projection G := lift_fst _ _

private theorem insert_first : insert G ≫ first G = projection G ≫ unitFrame G :=
  lift_fst _ _

private theorem insert_multiply : insert G ≫ multiply G = 𝟙 (E G) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h : (insert G ≫ multiply G) ≫ projection G = projection G := by
      rw [Category.assoc, multiply_projection, ← Category.assoc, insert_first,
        Category.assoc, section_projection, Category.comp_id]
    simpa only [projection, Category.id_comp] using h
  · have h : (insert G ≫ multiply G) ≫ snd (U G) (B G) = snd (U G) (B G) := by
      rw [Category.assoc, multiply, lift_snd, MonObj.comp_mul]
      have hl : insert G ≫ (first G ≫ snd (U G) (B G)) = 1 := by
        rw [← Category.assoc, insert_first, Category.assoc, unitFrame, lift_snd,
          MonObj.comp_one]
      rw [hl, insert, lift_snd, one_mul]
    simpa only [Category.id_comp] using h

private def overAt {X Y : Over (Spec (.of K))} (p : X ⟶ U G) (q : Y ⟶ U G)
    (f : X ⟶ Y) (h : f ≫ q = p) : Over.mk p.left ⟶ Over.mk q.left :=
  Over.homMk f.left (by
    change f.left ≫ q.left = p.left
    exact congrArg (fun z : X ⟶ U G => z.left) h)

private abbrev base := Over.mk (𝟙 (U G).left)
private abbrev product := Over.mk (projection G).left
private abbrev pair := Over.mk (first G ≫ projection G).left

private def p : product G ⟶ base G :=
  overAt G (projection G) (𝟙 (U G)) (projection G) (Category.comp_id _)

private def s : base G ⟶ product G :=
  overAt G (𝟙 (U G)) (projection G) (unitFrame G) (section_projection G)

private def f : pair G ⟶ product G :=
  overAt G (first G ≫ projection G) (projection G) (first G) rfl

private def m : pair G ⟶ product G :=
  overAt G (first G ≫ projection G) (projection G) (multiply G) (multiply_projection G)

private def i : product G ⟶ pair G :=
  overAt G (projection G) (first G ≫ projection G) (insert G) (by
    rw [← Category.assoc, insert_first, Category.assoc,
      section_projection, Category.comp_id])

private theorem im : i G ≫ m G = 𝟙 (product G) := by
  apply Over.OverMorphism.ext
  change (insert G).left ≫ (multiply G).left = 𝟙 _
  simpa only [Over.comp_left, Over.id_left] using
    congrArg (fun z : E G ⟶ E G => z.left) (insert_multiply G)

private theorem i_f : i G ≫ f G = p G ≫ s G := by
  apply Over.OverMorphism.ext
  change (insert G).left ≫ (first G).left =
    (projection G).left ≫ (unitFrame G).left
  simpa only [Over.comp_left] using
    congrArg (fun z : E G ⟶ E G => z.left) (insert_first G)

private theorem sp : s G ≫ p G = 𝟙 (base G) := by
  apply Over.OverMorphism.ext
  change (unitFrame G).left ≫ (projection G).left = 𝟙 _
  simpa only [Over.comp_left, Over.id_left] using
    congrArg (fun z : U G ⟶ U G => z.left) (section_projection G)

private theorem same_base : m G ≫ p G = f G ≫ p G := by
  apply Over.OverMorphism.ext
  change (multiply G).left ≫ (projection G).left =
    (first G).left ≫ (projection G).left
  simpa only [Over.comp_left] using
    congrArg (fun z : Q G ⟶ U G => z.left) (multiply_projection G)

private def c (chi : G.characters) : Γ((product G).left, ⊤) :=
  (snd (U G) (B G)).left.appTop (borelCharacterSection G chi)

private def v (chi : G.characters) : Γ((pair G).left, ⊤) :=
  (snd (E G) (B G)).left.appTop (borelCharacterSection G chi)

private theorem vi (chi : G.characters) : (i G).left.appTop (v G chi) = c G chi := by
  change ((insert G ≫ snd (E G) (B G)).left.appTop)
    (borelCharacterSection G chi) = _
  rw [insert, lift_snd]
  rfl

private theorem cs (chi : G.characters) : (s G).left.appTop (c G chi) = 1 := by
  change ((unitFrame G ≫ snd (U G) (B G)).left.appTop)
    (borelCharacterSection G chi) = 1
  rw [unitFrame, lift_snd]
  exact borelCharacterSection_one G chi (U G)

private theorem cm (chi : G.characters) :
    (m G).left.appTop (c G chi) = (f G).left.appTop (c G chi) * v G chi := by
  change ((multiply G ≫ snd (U G) (B G)).left.appTop)
      (borelCharacterSection G chi) =
    ((first G ≫ snd (U G) (B G)).left.appTop)
        (borelCharacterSection G chi) *
      (snd (E G) (B G)).left.appTop (borelCharacterSection G chi)
  rw [multiply, lift_snd]
  exact borelCharacterSection_mul G chi (Q G) _ _

/-- The regular character equations on the unipotent-times-Borel chart. -/
def localCharacterModule (chi : G.characters) : (U G).left.Modules :=
  equalizer (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (m G))
    (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (f G) ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (pair G) (v G chi))

/-- Evaluation at the identity Borel factor trivializes the character module. -/
def localCharacterIso (chi : G.characters) :
    SheafOfModules.unit (U G).left.ringCatSheaf ≅ localCharacterModule G chi :=
  (Scheme.Modules.pushforwardId (U G).left).symm.app
      (SheafOfModules.unit (U G).left.ringCatSheaf) ≪≫
    FrobeniusSplitting.CharacterLine.identityCharacterIso (U G).left (A := base G) (X := product G)
      (Q := pair G)
      (m G) (f G) (i G) (p G) (s G)
      (c G chi) (v G chi) (im G) (i_f G) (sp G) (same_base G)
      (vi G chi) (cs G chi) (cm G chi)

/-- The trivializing map is the original base function multiplied by the same full character. -/
theorem localCharacterIso_inclusion (chi : G.characters) :
    (localCharacterIso G chi).hom ≫
        equalizer.ι
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (X := pair G) (Y :=
            product G) (m G))
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (X := pair G) (Y :=
            product G) (f G) ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (pair G) (v G chi)) =
      (Scheme.Modules.pushforwardId (U G).left).inv.app
          (SheafOfModules.unit (U G).left.ringCatSheaf) ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap (U G).left (X := product G) (Y := base
          G) (p G) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (U G).left (product G) (c G chi) :=
            by
  let t := (Scheme.Modules.pushforwardId (U G).left).inv.app
    (SheafOfModules.unit (U G).left.ringCatSheaf)
  let e := FrobeniusSplitting.CharacterLine.identityCharacterIso (U G).left (A := base G) (X :=
    product G) (Q := pair G)
    (m G) (f G) (i G) (p G) (s G) (c G chi) (v G chi)
    (im G) (i_f G) (sp G) (same_base G) (vi G chi) (cs G chi) (cm G chi)
  have he := identityIso_inclusion (S := (U G).left)
    (A := base G) (X := product G) (Q := pair G)
    (m G) (f G) (i G) (p G) (s G) (c G chi) (v G chi)
    (im G) (i_f G) (sp G) (same_base G) (vi G chi) (cs G chi) (cm G chi)
  exact (Category.assoc t e.hom _).trans (congrArg (fun r => t ≫ r) he)

end SchubertGeometry.CharacterLine
