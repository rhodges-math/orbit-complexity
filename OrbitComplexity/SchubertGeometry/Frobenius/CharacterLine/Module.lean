import OrbitComplexity.SchubertGeometry.LineBundles.Modules.RegularAction
import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorTransitions
import OrbitComplexity.GroupActions.Varieties.SmoothProducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # The sheaf of regular functions with a full right Borel character -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private def functionsPullback {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z) :
    (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward (f ≫ p)).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (Scheme.Modules.pushforward p).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp f p).hom.app (SheafOfModules.unit X.ringCatSheaf)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev pair := (reductiveVariety G).toOver ⊗ (borelVariety G).toOver

private def pairFst : pair G ⟶ (reductiveVariety G).toOver := fst _ _
private def pairSnd : pair G ⟶ (borelVariety G).toOver := snd _ _
private def rightMul : pair G ⟶ (reductiveVariety G).toOver :=
  pairFst G * (pairSnd G ≫ borelInclusion G)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

private theorem rightMul_quotient :
    (rightMul G).left ≫ flagQuotient G = (pairFst G).left ≫ flagQuotient G := by
  have h : rightMul G ≫ flagQuotientMorphism G =
      pairFst G ≫ flagQuotientMorphism G := by
    apply Variety.mapPoints_injective
      (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
      (Y := flagVariety G)
    funext z
    let g := (reductivePointsMulEquiv G).symm
      (Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (pairFst G) z)
    let b := borelPointsMulEquiv G
      (Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := borelVariety G) (pairSnd G) z)
    have hg : Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (pairFst G) z = reductivePointsEquiv G g :=
      ((reductivePointsMulEquiv G).apply_symm_apply _).symm
    have hm : Variety.mapPoints
        (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
        (Y := reductiveVariety G) (rightMul G) z =
        reductivePointsEquiv G (g * (b : G.points)) := by
      rw [rightMul,
        mapPoints_mul
          (X := Variety.smoothProductVariety (reductiveVariety G) (borelVariety G))
          (H := reductiveVariety G),
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

private abbrev target :=
  (Scheme.Modules.pushforward ((pairFst G).left ≫ flagQuotient G)).obj
    (SheafOfModules.unit (pair G).left.ringCatSheaf)

private def characterPullback :
    (Scheme.Modules.pushforward (flagQuotient G)).obj
        (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf) ⟶ target G :=
  functionsPullback (rightMul G).left (flagQuotient G) ≫
    (Scheme.Modules.pushforwardCongr (rightMul_quotient G)).hom.app
      (SheafOfModules.unit (pair G).left.ringCatSheaf)

private def characterWeight (chi : G.characters) : Γ((pair G).left, ⊤) :=
  (pairSnd G).left.appTop
    ((Scheme.ΓSpecIso (.of G.borelAlgebra)).inv
      (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))

private def weightedPullback (chi : G.characters) :
    (Scheme.Modules.pushforward (flagQuotient G)).obj
        (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf) ⟶ target G :=
  functionsPullback (pairFst G).left (flagQuotient G) ≫
    (Scheme.Modules.pushforward ((pairFst G).left ≫ flagQuotient G)).map
      (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (pair G).left.ringCatSheaf)
        (characterWeight G chi))

/-- Regular functions on the flag torsor with the prescribed full right character. -/
def flagCharacterModule (chi : G.characters) : (flagVariety G).scheme.Modules :=
  equalizer (characterPullback G) (weightedPullback G chi)

/-- The character module includes into regular functions on the original quotient preimage. -/
def flagCharacterInclusion (chi : G.characters) :
    flagCharacterModule G chi ⟶
      (Scheme.Modules.pushforward (flagQuotient G)).obj
        (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf) :=
  equalizer.ι _ _

/-- A module map into torsor functions has the prescribed regular right-character equation. -/
def flagCharacterCondition (chi : G.characters) {M : (flagVariety G).scheme.Modules}
    (f : M ⟶ (Scheme.Modules.pushforward (flagQuotient G)).obj
      (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf)) : Prop :=
  f ≫ characterPullback G = f ≫ weightedPullback G chi

/-- A proved regular character equation gives its map to the character sheaf. -/
def flagCharacterLift (chi : G.characters) {M : (flagVariety G).scheme.Modules}
    (f : M ⟶ (Scheme.Modules.pushforward (flagQuotient G)).obj
      (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf))
    (h : flagCharacterCondition G chi f) : M ⟶ flagCharacterModule G chi :=
  equalizer.lift f h

/-- The character lift retains the original map into the functions on the torsor. -/
theorem flagCharacterLift_inclusion (chi : G.characters) {M : (flagVariety G).scheme.Modules}
    (f : M ⟶ (Scheme.Modules.pushforward (flagQuotient G)).obj
      (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf))
    (h : flagCharacterCondition G chi f) :
    flagCharacterLift G chi f h ≫ flagCharacterInclusion G chi = f :=
  equalizer.lift_ι _ _

end SchubertGeometry.CharacterLine
