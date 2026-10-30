import OrbitComplexity.SchubertGeometry.Deodhar.RelativeAction
import OrbitComplexity.GroupActions.Actions.Points

/-! # Coordinates of simple-extension fibres

A regular group frame identifies a simple-extension fibre with the additive line.
At a rational point, the inverse relative chart recovers its chosen simple-root parameter.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
namespace SchubertGeometry
open GroupActions
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private abbrev pointBase : Variety K where
  scheme := Spec (CommRingCat.of K)
  toSpec := 𝟙 _

private theorem iso_fibre_action {C : Type*} [Category C] [HasPullbacks C]
    [CartesianMonoidalCategory C] {X A Y B H F : C} [MonObj H] [ModObj H F]
    [Subsingleton (X ⟶ X)] (f : X ⟶ B) (p : Y ⟶ B) (g : X ⟶ H)
    (j : Y ⟶ F) (c : A ⟶ F) (e : X ⊗ A ≅ pullback f p)
    (he : ∀ (Z : C) (x : Z ⟶ X) (y : Z ⟶ A),
      lift x y ≫ (e.hom ≫ pullback.snd f p ≫ j) = (x ≫ g) • (y ≫ c))
    (q : X ⟶ Y) (hq : q ≫ p = f) : ∃ t : X ⟶ A, q ≫ j = g • (t ≫ c) := by
  let a := pullback.lift (𝟙 X) q (by simpa only [Category.id_comp] using hq.symm)
  let b := a ≫ e.inv
  have hbe : b ≫ e.hom = a := by simp only [b, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  have hb : b = lift (𝟙 X) (b ≫ snd X A) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact Subsingleton.elim _ _
    · rw [lift_snd]
  refine ⟨b ≫ snd X A, ?_⟩
  calc
    q ≫ j = (b ≫ e.hom) ≫ pullback.snd f p ≫ j := by
      rw [hbe]
      simp only [a, pullback.lift_snd_assoc]
    _ = b ≫ (e.hom ≫ pullback.snd f p ≫ j) := by simp only [Category.assoc]
    _ = g • ((b ≫ snd X A) ≫ c) := by
      rw [hb]
      simpa only [Category.id_comp, lift_snd] using he X (𝟙 X) (b ≫ snd X A)

set_option maxHeartbeats 400000 in
private theorem rankOne_fibre_action (w : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (x : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points)
    (r : G.points)
    (hr : flagVarietyPointsEquiv G (flagProjection G r) =
      Variety.mapPoints (schubertCellInclusion G w)
        (Variety.mapPoints (rankOneCellProjection G w i hi) x)) :
    ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (additiveVariety K).toOver,
      (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).pointsEquivOverHom x ≫
        schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
      (reductiveVariety G).pointsEquivOverHom (reductivePointsMulEquiv G r) •
        (t ≫ (simpleCellIso G i).hom ≫
          schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  let X := pointBase (K := K)
  let C := schubertCell G w
  let D := schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let A := additiveVariety K
  let p := rankOneCellProjection G w i hi
  let y := Variety.mapPoints p x
  let f : X.toOver ⟶ C.toOver := C.pointsEquivOverHom y
  let g : X.toOver ⟶ (reductiveVariety G).toOver :=
    (reductiveVariety G).pointsEquivOverHom (reductivePointsMulEquiv G r)
  have hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w := by
    exact congrArg ((flagVariety G).pointsEquivOverHom)
      ((flagQuotientMorphism_points G r).trans hr)
  let : Subsingleton (X.toOver ⟶ X.toOver) := ⟨fun a b => by
    apply Over.OverMorphism.ext
    have ha := a.w
    have hb := b.w
    change a.left ≫ 𝟙 _ = 𝟙 _ at ha
    change b.left ≫ 𝟙 _ = 𝟙 _ at hb
    simpa only [Category.comp_id] using ha.trans hb.symm⟩
  exact iso_fibre_action f p g
    (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    ((simpleCellIso G i).hom ≫
      schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (rankOneLiftIso G w i hi X f g hg)
    (lift_rankOneLiftIso_action G w i hi X f g hg)
    (D.pointsEquivOverHom x) rfl

set_option maxHeartbeats 400000 in
/-- A group frame over a projected cell point gives a chosen simple-root fibre coordinate. -/
theorem rankOneCellFibre_frame (w : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (x : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points)
    (r : G.points)
    (hr : flagVarietyPointsEquiv G (flagProjection G r) =
      Variety.mapPoints (schubertCellInclusion G w)
        (Variety.mapPoints (rankOneCellProjection G w i hi) x)) :
    ∃ t : K, Variety.mapPoints
      (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) x =
      flagVarietyPointsEquiv G (flagProjection G (r *
        gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) := by
  let D := schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let A := additiveVariety K
  let gp := reductivePointsMulEquiv G r
  let g := (reductiveVariety G).pointsEquivOverHom gp
  obtain ⟨c, hc⟩ := rankOne_fibre_action G w i hi x r hr
  let t := (additivePointsEquiv K).symm (A.pointsEquivOverHom.symm c)
  have ht : A.pointsEquivOverHom (additivePointsEquiv K t) = c := by
    dsimp only [t]
    rw [(additivePointsEquiv K).apply_symm_apply]
    exact A.pointsEquivOverHom.apply_symm_apply _
  refine ⟨t, ?_⟩
  have hx : Variety.mapPoints
      (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) x =
        gp • Variety.mapPoints ((simpleCellIso G i).hom ≫
          schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
          (additivePointsEquiv K t) := by
    apply (flagVariety G).pointsEquivOverHom.injective
    rw [Variety.pointsEquivOverHom_smul]
    change _ = g • (A.pointsEquivOverHom (additivePointsEquiv K t) ≫
      (simpleCellIso G i).hom ≫
        schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    rw [ht]
    exact hc
  rw [hx, simpleCellIso_points, flagVarietyAction_points]
  apply congrArg (flagVarietyPointsEquiv G)
  change flagProjection G (r * (gaParameterPoint (G.simpleRootMap i) t *
      (G.reflectionPoint i.val)⁻¹)) = _
  rw [mul_assoc]

end SchubertGeometry
