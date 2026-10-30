import OrbitComplexity.SchubertGeometry.Deodhar.ProductChart
import OrbitComplexity.SchubertGeometry.Deodhar.CellParameterPoints
import OrbitComplexity.SchubertGeometry.Deodhar.CellLifts
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections

/-! # Multiplication in increasing cell charts

The additive product chart agrees with the action of the canonical group-valued cell lift
on the simple cell. Rational root coordinates determine the equality of scheme morphisms.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

omit [IsAlgClosed K] [CharZero K] in
private theorem pointsHom_map {X Y : GroupActions.Variety K}
    (f : X.toOver ⟶ Y.toOver) (p : X.points) :
    X.pointsEquivOverHom p ≫ f = Y.pointsEquivOverHom (GroupActions.Variety.mapPoints f p) := rfl

private theorem tensorCell_hom : (rankOneTensorCellIso G w i hw).hom =
    (rankOneGaTensorIso G w).inv ≫ (rankOneGaCellIso G w i hw).hom := rfl

private theorem tensorCell_pair (p : (schubertUnipotent G w).points) (t : K) :
    lift ((schubertUnipotent G w).pointsEquivOverHom p)
      ((GroupActions.additiveVariety K).pointsEquivOverHom
        (GroupActions.additivePointsEquiv K t)) ≫
      ((rankOneTensorCellIso G w i hw).hom ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) =
      (flagVariety G).pointsEquivOverHom (flagVarietyPointsEquiv G (flagProjection G
        ((schubertUnipotentPointsEquiv G w p : G.points) * G.weylPoint w *
          gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹))) := by
  let x := (rankOneGaProductPointsEquiv G w).symm
    (p, GroupActions.additivePointsEquiv K t)
  let q := lift ((schubertUnipotent G w).pointsEquivOverHom p)
    ((GroupActions.additiveVariety K).pointsEquivOverHom
      (GroupActions.additivePointsEquiv K t))
  let e := rankOneGaTensorIso G w
  let c := (rankOneGaCellIso G w i hw).hom
  let j := schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)
  have hx : (rankOneGaProductVariety G w).pointsEquivOverHom x ≫ e.hom = q := by
    have h := rankOneGaTensorIso_points G w x
    simpa only [x, Equiv.apply_symm_apply] using h
  have hm : q ≫ e.inv = (rankOneGaProductVariety G w).pointsEquivOverHom x := by
    rw [← hx, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hc : q ≫ ((rankOneTensorCellIso G w i hw).hom ≫ j) =
      (rankOneGaProductVariety G w).pointsEquivOverHom x ≫ (c ≫ j) := by
    rw [tensorCell_hom, Category.assoc, ← Category.assoc q e.inv (c ≫ j), hm]
  exact hc.trans ((pointsHom_map (c ≫ j) x).trans
    (congrArg (flagVariety G).pointsEquivOverHom
      (rankOneGaCellIso_ambient_points G w i hw p t)))

private theorem cellProduct_hom : (rankOneCellProductIso G w i hw).hom =
    ((schubertCellIso G w).inv ⊗ₘ 𝟙 (GroupActions.additiveVariety K).toOver) ≫
      (rankOneTensorCellIso G w i hw).hom := rfl

private theorem compose_pair {C : Type*} [Category C] {A B D E F : C}
    (q : A ⟶ B) (τ : B ⟶ D) (c : D ⟶ E) (j : E ⟶ F) (k : B ⟶ E)
    (hk : k = τ ≫ c) (r : A ⟶ D) (hr : q ≫ τ = r) :
    q ≫ (k ≫ j) = r ≫ (c ≫ j) := by
  rw [hk, Category.assoc, ← Category.assoc q τ (c ≫ j), hr]

private theorem cellProduct_pair (z : (schubertCell G w).points) (t : K) :
    lift ((schubertCell G w).pointsEquivOverHom z)
      ((GroupActions.additiveVariety K).pointsEquivOverHom
        (GroupActions.additivePointsEquiv K t)) ≫
      ((rankOneCellProductIso G w i hw).hom ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) =
      (flagVariety G).pointsEquivOverHom (flagVarietyPointsEquiv G (flagProjection G
        ((schubertUnipotentPointsEquiv G w
          (GroupActions.Variety.mapPoints (schubertCellIso G w).inv z) : G.points) *
            G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
              (G.reflectionPoint i.val)⁻¹))) := by
  let p := GroupActions.Variety.mapPoints (schubertCellIso G w).inv z
  let q := lift ((schubertCell G w).pointsEquivOverHom z)
    ((GroupActions.additiveVariety K).pointsEquivOverHom (GroupActions.additivePointsEquiv K t))
  let τ := (schubertCellIso G w).inv ⊗ₘ 𝟙 (GroupActions.additiveVariety K).toOver
  let j := schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)
  have hq : q ≫ τ = lift ((schubertUnipotent G w).pointsEquivOverHom p)
      ((GroupActions.additiveVariety K).pointsEquivOverHom
        (GroupActions.additivePointsEquiv K t)) := by
    rw [lift_map, Category.comp_id, pointsHom_map]
  have hc : q ≫ ((rankOneCellProductIso G w i hw).hom ≫ j) =
      lift ((schubertUnipotent G w).pointsEquivOverHom p)
        ((GroupActions.additiveVariety K).pointsEquivOverHom
          (GroupActions.additivePointsEquiv K t)) ≫
          ((rankOneTensorCellIso G w i hw).hom ≫ j) := by
    exact compose_pair q τ (rankOneTensorCellIso G w i hw).hom j
      (rankOneCellProductIso G w i hw).hom (cellProduct_hom G w i hw) _ hq
  rw [hc]
  exact tensorCell_pair G w i hw p t

private theorem cellProduct_pair_action (z : (schubertCell G w).points) (t : K) :
    lift ((schubertCell G w).pointsEquivOverHom z)
      ((GroupActions.additiveVariety K).pointsEquivOverHom
        (GroupActions.additivePointsEquiv K t)) ≫
      ((rankOneCellProductIso G w i hw).hom ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) =
      (((schubertCell G w).pointsEquivOverHom z ≫ schubertCellLift G w) •
        ((GroupActions.additiveVariety K).pointsEquivOverHom
          (GroupActions.additivePointsEquiv K t) ≫ (simpleCellIso G i).hom ≫
            schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))) := by
  let p := GroupActions.Variety.mapPoints (schubertCellIso G w).inv z
  let a := GroupActions.Variety.mapPoints (schubertCellLift G w) z
  let b := GroupActions.Variety.mapPoints ((simpleCellIso G i).hom ≫
    schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))
      (GroupActions.additivePointsEquiv K t)
  have hab : a • b = flagVarietyPointsEquiv G (flagProjection G
      ((schubertUnipotentPointsEquiv G w p : G.points) * G.weylPoint w *
        gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) := by
    dsimp only [a, b]
    rw [schubertCellLift_points, simpleCellIso_points]
    change GroupActions.reductivePointsMulEquiv G
      ((schubertUnipotentPointsEquiv G w p : G.points) * G.weylPoint w) •
        flagVarietyPointsEquiv G (flagProjection G
          (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) = _
    rw [flagVarietyAction_points]
    apply congrArg (flagVarietyPointsEquiv G)
    change flagProjection G ((_ * _) * (_ * _)) = flagProjection G (((_ * _) * _) * _)
    simp only [mul_assoc]
  have ha := pointsHom_map (schubertCellLift G w) z
  have hb := pointsHom_map ((simpleCellIso G i).hom ≫ schubertCellInclusion G
    (RootPairing.weylGroup.ofIdx G.rootSystem i)) (GroupActions.additivePointsEquiv K t)
  calc
    _ = (flagVariety G).pointsEquivOverHom (flagVarietyPointsEquiv G
        (flagProjection G ((schubertUnipotentPointsEquiv G w p : G.points) *
          G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
            (G.reflectionPoint i.val)⁻¹))) := cellProduct_pair G w i hw z t
    _ = (flagVariety G).pointsEquivOverHom (a • b) :=
      congrArg (flagVariety G).pointsEquivOverHom hab.symm
    _ = (GroupActions.reductiveVariety G).pointsEquivOverHom a •
        (flagVariety G).pointsEquivOverHom b :=
      GroupActions.Variety.pointsEquivOverHom_smul
        (GroupActions.reductiveVariety G) (flagVariety G) a b
    _ = _ := congrArg₂ (fun m x => m • x) ha.symm hb.symm

private instance gaIntegral : IsIntegral (GroupActions.additiveVariety K).scheme := by
  change IsIntegral (Spec (CommRingCat.of (SymmetricAlgebra K K)))
  infer_instance

omit [CharZero K] in
private theorem morphism_eq_of_pairs
    (A B Y : GroupActions.Variety K) [IrreducibleSpace A.scheme]
    [IrreducibleSpace B.scheme] (f g : A.toOver ⊗ B.toOver ⟶ Y.toOver)
    (h : ∀ a b, lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) ≫ f =
      lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) ≫ g) : f = g := by
  let P := GroupActions.Variety.productVariety A B
  apply GroupActions.Variety.mapPoints_injective (X := P) (Y := Y)
  funext p
  apply Y.pointsEquivOverHom.injective
  let a := A.pointsEquivOverHom.symm (P.pointsEquivOverHom p ≫ fst A.toOver B.toOver)
  let b := B.pointsEquivOverHom.symm (P.pointsEquivOverHom p ≫ snd A.toOver B.toOver)
  have hp : P.pointsEquivOverHom p =
      lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [lift_fst, lift_snd, a, b, Equiv.apply_symm_apply]
  change P.pointsEquivOverHom p ≫ f = P.pointsEquivOverHom p ≫ g
  rw [hp]
  exact h a b

private theorem pair_action {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B M Y Z : C} [MonObj M] [ModObj M Y]
    (x : Z ⟶ A) (y : Z ⟶ B) (m : A ⟶ M) (n : B ⟶ Y) :
    lift x y ≫ ((fst A B ≫ m) • (snd A B ≫ n)) = (x ≫ m) • (y ≫ n) := by
  rw [ModObj.comp_smul, lift_fst_assoc, lift_snd_assoc]

omit [CharZero K] in
private theorem morphism_eq_of_actions
    (A B H Y : GroupActions.Variety K) [IrreducibleSpace A.scheme]
    [IrreducibleSpace B.scheme] [GrpObj H.toOver] [ModObj H.toOver Y.toOver]
    (m : A.toOver ⟶ H.toOver) (n : B.toOver ⟶ Y.toOver)
    (f : A.toOver ⊗ B.toOver ⟶ Y.toOver)
    (h : ∀ a b, lift (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) ≫ f =
      (A.pointsEquivOverHom a ≫ m) • (B.pointsEquivOverHom b ≫ n)) :
    f = (fst A.toOver B.toOver ≫ m) • (snd A.toOver B.toOver ≫ n) := by
  apply morphism_eq_of_pairs A B Y
  intro a b
  exact (h a b).trans (pair_action (A.pointsEquivOverHom a) (B.pointsEquivOverHom b) m n).symm

/-- The increasing-cell product chart multiplies the canonical cell lift and simple flag. -/
theorem rankOneCellProductIso_action :
    (rankOneCellProductIso G w i hw).hom ≫ schubertCellInclusion G
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i) =
      ((fst (schubertCell G w).toOver (GroupActions.additiveVariety K).toOver ≫
        schubertCellLift G w) •
        (snd (schubertCell G w).toOver (GroupActions.additiveVariety K).toOver ≫
          (simpleCellIso G i).hom ≫
            schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))) := by
  apply morphism_eq_of_actions (schubertCell G w) (GroupActions.additiveVariety K)
    (GroupActions.reductiveVariety G) (flagVariety G) (schubertCellLift G w)
    ((simpleCellIso G i).hom ≫
      schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i))
  intro z a
  obtain ⟨t, rfl⟩ := (GroupActions.additivePointsEquiv K).surjective a
  exact cellProduct_pair_action G w i hw z t

end
end SchubertGeometry
