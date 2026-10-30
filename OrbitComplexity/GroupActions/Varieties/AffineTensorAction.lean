import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.GroupActions.Varieties.AffineProduct

/-!
# Tensor coordinates of affine action families

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

noncomputable section

namespace GroupActions

attribute [local instance] Over.cartesianMonoidalCategory

universe u

variable {R A H D : Type u} [CommRing R] [CommRing A] [CommRing H] [CommRing D]
    [Algebra R A] [Algebra R H] [Algebra R D]

/-- The spectrum of an algebra map, with its original relative structure. -/
def algebraSpecMap (f : A →ₐ[R] D) :
    (Spec (.of D)).asOver (Spec (.of R)) ⟶
      (Spec (.of A)).asOver (Spec (.of R)) :=
  (algSpec (.of R)).map (CommAlgCat.ofHom f).op

/-- Forgetting the base from a relative spectrum map gives the ordinary map. -/
theorem algebraSpecMap_left (f : A →ₐ[R] D) :
    (algebraSpecMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

/-- Algebra-spectrum maps reverse composition, over arbitrary coefficient rings. -/
theorem algebraSpecMap_comp {B : Type u} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    algebraSpecMap (g.comp f) = algebraSpecMap g ≫ algebraSpecMap f :=
  (algSpec (.of R)).map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

private theorem overPair_fst {S : Scheme.{u}} {P X Y : Over S}
    (f : P ⟶ X) (g : P ⟶ Y) :
    (lift f g).left ≫ pullback.fst X.hom Y.hom = f.left := by
  change (lift f g ≫ fst X Y).left = f.left
  exact congrArg (fun k : P ⟶ X => k.left) (lift_fst f g)

private theorem overPair_snd {S : Scheme.{u}} {P X Y : Over S}
    (f : P ⟶ X) (g : P ⟶ Y) :
    (lift f g).left ≫ pullback.snd X.hom Y.hom = g.left := by
  change (lift f g ≫ snd X Y).left = g.left
  exact congrArg (fun k : P ⟶ Y => k.left) (lift_snd f g)

/-- The tensor-evaluation spectrum is the same specified pair of affine maps. -/
theorem affineTensor_pair (t : H →ₐ[R] D) (x : A →ₐ[R] D) :
    (lift (algebraSpecMap t) (algebraSpecMap x)).left =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lift t x (fun _ _ => .all _ _)).toRingHom) ≫
          (pullbackSpecIso R H A).inv := by
  let l : Spec (.of D) ⟶ pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (lift (algebraSpecMap t) (algebraSpecMap x)).left
  have hfst : l ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom t.toRingHom) :=
    overPair_fst (algebraSpecMap t) (algebraSpecMap x)
  have hsnd : l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom x.toRingHom) :=
    overPair_snd (algebraSpecMap t) (algebraSpecMap x)
  change l = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift t x (fun _ _ => .all _ _)).toRingHom) ≫
    (pullbackSpecIso R H A).inv
  apply pullback.hom_ext
  · rw [hfst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    congr 1
    ext a
    simp
  · rw [hsnd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    congr 1
    ext a
    simp

/-- An action with given tensor coordinates has the expected arbitrary-algebra
evaluation formula. The action map itself is an arbitrary morphism. -/
theorem affineTensor_action
    (a : (Spec (.of H)).asOver (Spec (.of R)) ⊗
      (Spec (.of A)).asOver (Spec (.of R)) ⟶
        (Spec (.of A)).asOver (Spec (.of R)))
    (θ : A →ₐ[R] H ⊗[R] A)
    (ha : a.left = (pullbackSpecIso R H A).hom ≫
      Spec.map (CommRingCat.ofHom θ.toRingHom))
    (t : H →ₐ[R] D) (x : A →ₐ[R] D) :
    (lift (algebraSpecMap t) (algebraSpecMap x) ≫ a).left =
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.lift t x (fun _ _ => .all _ _)).comp θ).toRingHom) := by
  let a₀ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ Spec (.of A) := a.left
  let l : Spec (.of D) ⟶ pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (lift (algebraSpecMap t) (algebraSpecMap x)).left
  have hPair : l = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift t x (fun _ _ => .all _ _)).toRingHom) ≫
        (pullbackSpecIso R H A).inv := affineTensor_pair t x
  have hAction : a₀ = (pullbackSpecIso R H A).hom ≫
      Spec.map (CommRingCat.ofHom θ.toRingHom) := ha
  change l ≫ a₀ = Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.lift t x (fun _ _ => .all _ _)).comp θ).toRingHom)
  rw [hPair, hAction]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  rfl

end GroupActions
