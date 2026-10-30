import OrbitComplexity.GroupActions.Actions.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Equivariant intersections and transverse action pairs

Independent group actions untwist the pullback of their paired action map into the
product of the two group objects with the original intersection.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions
noncomputable section
universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (B O F : C) [GrpObj B] [GrpObj O] [ModObj B F] [ModObj O F]

/-- The paired action sends a flag and two independent group coordinates to their images. -/
def transverseAction : (B ⊗ O) ⊗ F ⟶ F ⊗ F :=
  lift ((fst (B ⊗ O) F ≫ fst B O) • snd (B ⊗ O) F)
    ((fst (B ⊗ O) F ≫ snd B O) • snd (B ⊗ O) F)

private theorem transverseAction_fst : transverseAction B O F ≫ fst F F =
    (fst (B ⊗ O) F ≫ fst B O) • snd (B ⊗ O) F := by
  simp only [transverseAction, lift_fst]

private theorem transverseAction_snd : transverseAction B O F ≫ snd F F =
    (fst (B ⊗ O) F ≫ snd B O) • snd (B ⊗ O) F := by
  simp only [transverseAction, lift_snd]

private theorem lift_transverseAction {T : C} (h : T ⟶ B ⊗ O) (z : T ⟶ F) :
    lift h z ≫ transverseAction B O F =
      lift ((h ≫ fst B O) • z) ((h ≫ snd B O) • z) := by
  simp [transverseAction, ModObj.comp_smul]

variable [HasPullbacks C] {X Y : C} [ModObj B X] [ModObj O Y]
  (f : X ⟶ F) (g : Y ⟶ F) [IsModHom B f] [IsModHom O g]

private def pairedLift {T : C} (h : T ⟶ B ⊗ O) (x : T ⟶ X) (y : T ⟶ Y)
    (hxy : x ≫ f = y ≫ g) : T ⟶ pullback (transverseAction B O F) (f ⊗ₘ g) :=
  pullback.lift (lift h (x ≫ f))
    (lift ((h ≫ fst B O) • x) ((h ≫ snd B O) • y)) (by
      rw [lift_transverseAction]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, Category.assoc, tensorHom_fst, lift_fst_assoc]
        exact (IsModHom.map_smul f (h ≫ fst B O) x).symm
      · simp only [lift_snd, Category.assoc, tensorHom_snd, lift_snd_assoc]
        rw [IsModHom.map_smul, hxy])

@[reassoc] private theorem pairedLift_fst {T : C}
    (h : T ⟶ B ⊗ O) (x : T ⟶ X) (y : T ⟶ Y)
    (hxy : x ≫ f = y ≫ g) :
    pairedLift B O F f g h x y hxy ≫
        pullback.fst (transverseAction B O F) (f ⊗ₘ g) = lift h (x ≫ f) := by
  simp only [pairedLift, pullback.lift_fst]

@[reassoc] private theorem pairedLift_snd {T : C}
    (h : T ⟶ B ⊗ O) (x : T ⟶ X) (y : T ⟶ Y)
    (hxy : x ≫ f = y ≫ g) :
    pairedLift B O F f g h x y hxy ≫
        pullback.snd (transverseAction B O F) (f ⊗ₘ g) =
      lift ((h ≫ fst B O) • x) ((h ≫ snd B O) • y) := by
  simp only [pairedLift, pullback.lift_snd]

private def intersectionForward : (B ⊗ O) ⊗ pullback f g ⟶
    pullback (transverseAction B O F) (f ⊗ₘ g) :=
  pairedLift B O F f g (fst (B ⊗ O) (pullback f g))
    (snd (B ⊗ O) (pullback f g) ≫ pullback.fst f g)
    (snd (B ⊗ O) (pullback f g) ≫ pullback.snd f g)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc])

private abbrev pairGroup : pullback (transverseAction B O F) (f ⊗ₘ g) ⟶ B ⊗ O :=
  pullback.fst (transverseAction B O F) (f ⊗ₘ g) ≫ fst (B ⊗ O) F

private abbrev pairFlag : pullback (transverseAction B O F) (f ⊗ₘ g) ⟶ F :=
  pullback.fst (transverseAction B O F) (f ⊗ₘ g) ≫ snd (B ⊗ O) F

private abbrev pairFirst : pullback (transverseAction B O F) (f ⊗ₘ g) ⟶ X :=
  pullback.snd (transverseAction B O F) (f ⊗ₘ g) ≫ fst X Y

private abbrev pairSecond : pullback (transverseAction B O F) (f ⊗ₘ g) ⟶ Y :=
  pullback.snd (transverseAction B O F) (f ⊗ₘ g) ≫ snd X Y

omit [ModObj B X] [ModObj O Y] [IsModHom B f] [IsModHom O g] in
private theorem pairFirst_factor : pairFirst B O F f g ≫ f =
    (pairGroup B O F f g ≫ fst B O) • pairFlag B O F f g := by
  have h := congrArg (fun t => t ≫ fst F F)
    (pullback.condition (f := transverseAction B O F) (g := f ⊗ₘ g))
  simpa only [pairFirst, pairGroup, pairFlag, Category.assoc,
    transverseAction_fst, tensorHom_fst,
    ModObj.comp_smul] using h.symm

omit [ModObj B X] [ModObj O Y] [IsModHom B f] [IsModHom O g] in
private theorem pairSecond_factor : pairSecond B O F f g ≫ g =
    (pairGroup B O F f g ≫ snd B O) • pairFlag B O F f g := by
  have h := congrArg (fun t => t ≫ snd F F)
    (pullback.condition (f := transverseAction B O F) (g := f ⊗ₘ g))
  simpa only [pairSecond, pairGroup, pairFlag, Category.assoc,
    transverseAction_snd, tensorHom_snd,
    ModObj.comp_smul] using h.symm

omit [ModObj O Y] [IsModHom O g] in
private theorem untwistFirst_factor :
    ((pairGroup B O F f g ≫ fst B O)⁻¹ • pairFirst B O F f g) ≫ f =
      pairFlag B O F f g := by
  rw [IsModHom.map_smul, pairFirst_factor, inv_smul_smul]

omit [ModObj B X] [IsModHom B f] in
private theorem untwistSecond_factor :
    ((pairGroup B O F f g ≫ snd B O)⁻¹ • pairSecond B O F f g) ≫ g =
      pairFlag B O F f g := by
  rw [IsModHom.map_smul, pairSecond_factor, inv_smul_smul]

private def intersectionInverse : pullback (transverseAction B O F) (f ⊗ₘ g) ⟶
    (B ⊗ O) ⊗ pullback f g :=
  lift (pairGroup B O F f g)
    (pullback.lift
      ((pairGroup B O F f g ≫ fst B O)⁻¹ • pairFirst B O F f g)
      ((pairGroup B O F f g ≫ snd B O)⁻¹ • pairSecond B O F f g)
      ((untwistFirst_factor B O F f g).trans (untwistSecond_factor B O F f g).symm))

private theorem forward_inverse :
    intersectionForward B O F f g ≫ intersectionInverse B O F f g = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [intersectionInverse, intersectionForward, pairedLift_fst_assoc, pairGroup,
      Category.assoc]
  · apply pullback.hom_ext
    · simp [intersectionInverse, intersectionForward, pairedLift_fst_assoc, pairedLift_snd_assoc,
        pairGroup, pairFirst, ModObj.comp_smul, GrpObj.comp_inv, Category.assoc]
    · simp [intersectionInverse, intersectionForward, pairedLift_fst_assoc, pairedLift_snd_assoc,
        pairGroup, pairSecond, ModObj.comp_smul, GrpObj.comp_inv, Category.assoc]

private theorem inverse_forward :
    intersectionInverse B O F f g ≫ intersectionForward B O F f g = 𝟙 _ := by
  apply pullback.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [intersectionForward, Category.assoc, pairedLift_fst, lift_fst,
        intersectionInverse, Category.id_comp]
    · simpa only [intersectionForward, Category.assoc, pairedLift_fst_assoc, lift_snd,
        lift_snd_assoc, intersectionInverse, pullback.lift_fst_assoc, Category.id_comp] using
        untwistFirst_factor B O F f g
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [intersectionForward, Category.assoc, pairedLift_snd, lift_fst,
        ModObj.comp_smul, intersectionInverse]
      rw [← Category.assoc, lift_fst]
      simp
    · simp only [intersectionForward, Category.assoc, pairedLift_snd, lift_snd,
        ModObj.comp_smul, intersectionInverse]
      rw [← Category.assoc, lift_fst]
      simp

/-- Equivariant maps untwist the pullback of the paired action into the group product
with their original fibre product. -/
def equivariantIntersectionIso : (B ⊗ O) ⊗ pullback f g ≅
    pullback (transverseAction B O F) (f ⊗ₘ g) where
  hom := intersectionForward B O F f g
  inv := intersectionInverse B O F f g
  hom_inv_id := forward_inverse B O F f g
  inv_hom_id := inverse_forward B O F f g

/-- The transverse comparison retains both group coordinates and the common flag. -/
theorem equivariantIntersectionIso_fst : (equivariantIntersectionIso B O F f g).hom ≫
    pullback.fst (transverseAction B O F) (f ⊗ₘ g) =
      lift (fst (B ⊗ O) (pullback f g))
        (snd (B ⊗ O) (pullback f g) ≫ pullback.fst f g ≫ f) := by
  simp only [equivariantIntersectionIso, intersectionForward, pairedLift_fst,
    Category.assoc]

/-- The second comparison projection acts separately on the two original factors. -/
theorem equivariantIntersectionIso_snd : (equivariantIntersectionIso B O F f g).hom ≫
    pullback.snd (transverseAction B O F) (f ⊗ₘ g) =
      lift ((fst (B ⊗ O) (pullback f g) ≫ fst B O) •
        (snd (B ⊗ O) (pullback f g) ≫ pullback.fst f g))
        ((fst (B ⊗ O) (pullback f g) ≫ snd B O) •
          (snd (B ⊗ O) (pullback f g) ≫ pullback.snd f g)) := by
  simp only [equivariantIntersectionIso, intersectionForward, pairedLift_snd]

end
end GroupActions
