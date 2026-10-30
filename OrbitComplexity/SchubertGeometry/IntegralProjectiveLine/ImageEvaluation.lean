import OrbitComplexity.FrobeniusSplitting.Modules.FrobeniusImage
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.FrobeniusEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Evaluation over the Frobenius-image ring sheaf -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting GroupActions
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

private def scalarChange {X : Scheme.{u}}
    {R S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u}}
    (e : R ≅ S) : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S :=
  SheafOfModules.restrictScalars e.inv

private def unitChangeMap {X : Scheme.{u}}
    {R S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u}}
    (e : R ≅ S) : SheafOfModules.unit S ⟶ (scalarChange e).obj (SheafOfModules.unit R) where
  val.app U := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (e.inv.hom.app U))
    (fun r => by
      ext m
      exact ((e.inv.hom.app U).hom.map_mul _ _).symm)
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality i) a

private theorem unitChangeMap_isIso {X : Scheme.{u}}
    {R S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u}}
    (e : R ≅ S) : IsIso (unitChangeMap e) := by
  let F := sheafCompose (_root_.Opens.grothendieckTopology X)
    (forget₂ RingCat.{u} AddCommGrpCat.{u})
  have hi : IsIso (F.map e.inv) := inferInstance
  have h : IsIso ((SheafOfModules.toSheaf S).map (unitChangeMap e)) := hi
  let : IsIso ((SheafOfModules.toSheaf S).map (unitChangeMap e)) := h
  exact isIso_of_reflects_iso (unitChangeMap e) (SheafOfModules.toSheaf S)

private def freeChangeIso {X : Scheme.{u}}
    {R S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u}}
    (e : R ≅ S) (I : Type u) [Finite I] : SheafOfModules.free (R := S) I ≅
      (scalarChange e).obj (SheafOfModules.free (R := R) I) := by
  let F := SheafOfModules.restrictScalars e.inv
  let : PreservesColimitsOfShape (Discrete I) F := inferInstance
  exact SheafOfModules.mapFreeIso F I
    (@asIso _ _ _ _ (unitChangeMap (X := X) e) (unitChangeMap_isIso (X := X) e))

private theorem freeChange_generator {X : Scheme.{u}}
    {R S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u}}
    (e : R ≅ S) (I : Type u) [Finite I] (k : I) :
    SheafOfModules.ιFree k ≫ (freeChangeIso e I).hom =
      unitChangeMap e ≫ (scalarChange e).map (SheafOfModules.ιFree k) := by
  dsimp only [freeChangeIso]
  exact SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _

private def undoRestriction {X : Scheme.{u}}
    {R S : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u}}
    (e : R ≅ S) (α : S ⟶ R) (β : R ⟶ R) (h : e.hom ≫ α = β)
    (M : SheafOfModules.{u} R) :
    (scalarChange e).obj ((SheafOfModules.restrictScalars β).obj M) ≅
      (SheafOfModules.restrictScalars α).obj M := by
  refine (SheafOfModules.fullyFaithfulForget S).preimageIso ?_
  refine PresheafOfModules.isoMk (fun U => ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext s
    change (α.hom.app U).hom r • (show M.val.obj U from s) =
      ((β.hom.app U).hom ((e.inv.hom.app U).hom r)) • (show M.val.obj U from s)
    have hp : e.inv ≫ β = α := by
      rw [← h, Iso.inv_hom_id_assoc]
    have hr := congrArg (fun t : S ⟶ R => (t.hom.app U).hom r) hp
    change (β.hom.app U).hom ((e.inv.hom.app U).hom r) = (α.hom.app U).hom r at hr
    rw [hr]
  · intro U V i
    ext s
    rfl

private def powerRestrictionIso (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M : X.Modules) :
    frobeniusRestriction C p base M ≅
      (SheafOfModules.restrictScalars (sheafFrobenius C p base)).obj M := Iso.refl _

/-- The Laurent-matched degree-p-minus-one module, with scalars restricted along
the inclusion of pth-power functions. -/
def projectiveImageModule (K : Type u) [Field K] (p : ℕ) [ExpChar K p] :
    SheafOfModules.{u}
      (frobeniusImageSheaf K p (projectiveToSpec K (ULift.{u} (Fin 2)))) :=
  (SheafOfModules.restrictScalars
    (frobeniusImageInclusion K p (projectiveToSpec K (ULift.{u} (Fin 2))))).obj
      (ProjectiveLine.projectiveTransitionModule K (p - 1))

private def targetImageIso (K : Type u) [Field K] (p : ℕ) [ExpChar K p] :
    (scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
      (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).obj
        (frobeniusRestriction K p (projectiveToSpec K (ULift.{u} (Fin 2)))
          (ProjectiveLine.projectiveTransitionModule K (p - 1))) ≅ projectiveImageModule K p :=
  (scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
    (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).mapIso
      (powerRestrictionIso K p (projectiveToSpec K (ULift.{u} (Fin 2)))
        (ProjectiveLine.projectiveTransitionModule K (p - 1))) ≪≫
    undoRestriction
      (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))
      (frobeniusImageInclusion K p (projectiveToSpec K (ULift.{u} (Fin 2))))
      (sheafFrobenius K p (projectiveToSpec K (ULift.{u} (Fin 2))))
      (frobeniusImageIso_factor K p (projectiveToSpec K (ULift.{u} (Fin 2))))
      (ProjectiveLine.projectiveTransitionModule K (p - 1))

/-- The global evaluation over the absolute Frobenius-image ring sheaf;
the coefficient comparison uses inverse Frobenius-to-image, not ordinary inclusion. -/
def projectiveImageEval (K : Type u) [Field K] (p : ℕ) [ExpChar K p] :
    SheafOfModules.free
      (R := frobeniusImageSheaf K p (projectiveToSpec K (ULift.{u} (Fin 2))))
      (ULift.{u} (Fin p)) ⟶ projectiveImageModule K p :=
  (freeChangeIso (X := projectiveScheme K (ULift.{u} (Fin 2)))
    (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))
    (ULift.{u} (Fin p))).hom ≫
    (scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
      (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).map
        (ProjectiveLine.projectiveFrobeniusEval K p) ≫ (targetImageIso K p).hom

/-- Perfect coefficients make this image-ring evaluation an isomorphism. -/
theorem projectiveImageEval_isIso (K : Type u) [Field K] (p : ℕ)
    [ExpChar K p] [PerfectRing K p] : IsIso (projectiveImageEval K p) := by
  have hm : IsIso ((scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
      (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).map
        (ProjectiveLine.projectiveFrobeniusEval K p)) :=
    @Functor.map_isIso _ _ _ _ _ _
      (scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
        (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2)))))
      (ProjectiveLine.projectiveFrobeniusEval K p)
      (ProjectiveLine.projectiveFrobeniusEval_isIso K p)
  let : IsIso ((scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
      (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).map
        (ProjectiveLine.projectiveFrobeniusEval K p)) := hm
  unfold projectiveImageEval
  infer_instance

private theorem imageEval_generator (K : Type u) [Field K] (p : ℕ) [ExpChar K p]
    (k : ULift.{u} (Fin p)) :
    SheafOfModules.ιFree k ≫ projectiveImageEval K p =
      unitChangeMap (X := projectiveScheme K (ULift.{u} (Fin 2)))
        (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2)))) ≫
      (scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
        (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).map
        (SheafOfModules.ιFree k ≫ ProjectiveLine.projectiveFrobeniusEval K p) ≫
        (targetImageIso K p).hom := by
  unfold projectiveImageEval
  erw [← Category.assoc, ← Category.assoc, freeChange_generator]
  have hm := (scalarChange (X := projectiveScheme K (ULift.{u} (Fin 2)))
    (frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2))))).map_comp
      (SheafOfModules.ιFree (R := (projectiveScheme K (ULift.{u} (Fin 2))).ringCatSheaf) k)
      (ProjectiveLine.projectiveFrobeniusEval K p)
  erw [hm]
  simp only [Category.assoc]

private theorem targetImageIso_value (K : Type u) [Field K] (p : ℕ) [ExpChar K p]
    (U : (projectiveScheme K (ULift.{u} (Fin 2))).Opensᵒᵖ)
    (s : (frobeniusRestriction K p (projectiveToSpec K (ULift.{u} (Fin 2)))
      (ProjectiveLine.projectiveTransitionModule K (p - 1))).val.obj U) :
    ((targetImageIso K p).hom.val.app U).hom s =
      (show (projectiveImageModule K p).val.obj U from s) := rfl

/-- Each image-ring free generator evaluates to the global monomial
section used by the Frobenius evaluation, on every open. -/
theorem projectiveImageEval_generators (K : Type u) [Field K] (p : ℕ) [ExpChar K p]
    (k : ULift.{u} (Fin p)) (U : (projectiveScheme K (ULift.{u} (Fin 2))).Opensᵒᵖ) :
    ((SheafOfModules.ιFree
      (R := frobeniusImageSheaf K p (projectiveToSpec K (ULift.{u} (Fin 2)))) k ≫
        projectiveImageEval K p).val.app U).hom
      (1 : (frobeniusImageSheaf K p (projectiveToSpec K (ULift.{u} (Fin 2)))).obj.obj U) =
    (SheafOfModules.freeHomEquiv
      (frobeniusRestriction K p (projectiveToSpec K (ULift.{u} (Fin 2)))
        (ProjectiveLine.projectiveTransitionModule K (p - 1)))
      (ProjectiveLine.projectiveFrobeniusEval K p) k).val U := by
  have h := congrArg
    (fun f : SheafOfModules.unit
        (frobeniusImageSheaf K p (projectiveToSpec K (ULift.{u} (Fin 2)))) ⟶
          projectiveImageModule K p =>
      (f.val.app U).hom
        (1 : (frobeniusImageSheaf K p (projectiveToSpec K (ULift.{u} (Fin 2)))).obj.obj U))
    (imageEval_generator K p k)
  change _ = ((targetImageIso K p).hom.val.app U).hom
    (((SheafOfModules.ιFree
      (R := (projectiveScheme K (ULift.{u} (Fin 2))).ringCatSheaf) k ≫
        ProjectiveLine.projectiveFrobeniusEval K p).val.app U).hom
      (((frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2)))).inv.hom.app U).hom
        (1 : (frobeniusImageSheaf K p
          (projectiveToSpec K (ULift.{u} (Fin 2)))).obj.obj U))) at h
  have hone := ((frobeniusImageIso K p
    (projectiveToSpec K (ULift.{u} (Fin 2)))).inv.hom.app U).hom.map_one
  have ht := targetImageIso_value K p U
    (((SheafOfModules.ιFree
      (R := (projectiveScheme K (ULift.{u} (Fin 2))).ringCatSheaf) k ≫
        ProjectiveLine.projectiveFrobeniusEval K p).val.app U).hom
      (((frobeniusImageIso K p (projectiveToSpec K (ULift.{u} (Fin 2)))).inv.hom.app U).hom
        (1 : (frobeniusImageSheaf K p
          (projectiveToSpec K (ULift.{u} (Fin 2)))).obj.obj U)))
  have hu := congrArg
    (fun r : (projectiveScheme K (ULift.{u} (Fin 2))).ringCatSheaf.obj.obj U =>
      ((SheafOfModules.ιFree
        (R := (projectiveScheme K (ULift.{u} (Fin 2))).ringCatSheaf) k ≫
          ProjectiveLine.projectiveFrobeniusEval K p).val.app U).hom r) hone
  exact h.trans (ht.trans hu)

end SchubertGeometry.ProjectiveLine
