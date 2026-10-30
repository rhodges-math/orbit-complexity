import OrbitComplexity.GroupActions.Rosenlicht.BaseFields
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# Actions on function fields

An action on a scheme by automorphisms acts on its function field by inverse pullback.
This convention turns the contravariant pullback into a left action.

## Main definitions

* `functionFieldAction`: the action on the function field induced by scheme automorphisms.

## Main results

* `functionFieldMap_equivariant`: pullback of an equivariant morphism is equivariant.
* `functionFieldAction_smulComm`: automorphisms over an affine base act by base-ring
  algebra automorphisms.

## Implementation notes

An action by scheme automorphisms is expressed as a monoid homomorphism to
`CategoryTheory.Aut X`.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

variable {X : Scheme.{u}}
variable {M : Type v} [Monoid M]

private instance aut_inv_isIso (e : Aut X) : IsIso e.inv := Iso.isIso_inv e

section Irreducible

variable [IrreducibleSpace X]

/-- An action by scheme automorphisms induces a semiring action on the function field
by pullback along inverse automorphisms. -/
@[instance_reducible]
def functionFieldAction (ρ : M →* Aut X) : MulSemiringAction M X.functionField where
  smul m x := functionFieldMap (ρ m).inv x
  one_smul x := by
    change functionFieldMap (ρ 1).inv x = x
    rw [map_one]
    change functionFieldMap (𝟙 X) x = x
    rw [functionFieldMap_id]
    rfl
  mul_smul m n x := by
    change functionFieldMap (ρ (m * n)).inv x =
      functionFieldMap (ρ m).inv (functionFieldMap (ρ n).inv x)
    rw [map_mul]
    change functionFieldMap ((ρ m).inv ≫ (ρ n).inv) x = _
    rw [functionFieldMap_comp]
    rfl
  smul_zero m := (functionFieldMap (ρ m).inv).map_zero
  smul_add m x y := (functionFieldMap (ρ m).inv).map_add x y
  smul_one m := (functionFieldMap (ρ m).inv).map_one
  smul_mul m x y := (functionFieldMap (ρ m).inv).map_mul x y

omit [IrreducibleSpace X] in
private lemma aut_inv_natural {Y : Scheme.{u}} (a : X ≅ X) (b : Y ≅ Y) (f : X ⟶ Y)
    (h : a.hom ≫ f = f ≫ b.hom) : a.inv ≫ f = f ≫ b.inv := by
  calc
    a.inv ≫ f = (a.inv ≫ f) ≫ (b.hom ≫ b.inv) := by
      rw [b.hom_inv_id, Category.comp_id]
    _ = a.inv ≫ (f ≫ b.hom) ≫ b.inv := by simp only [Category.assoc]
    _ = a.inv ≫ (a.hom ≫ f) ≫ b.inv := by rw [← h]
    _ = f ≫ b.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

private lemma functionFieldMap_congr {Y : Scheme.{u}} [IrreducibleSpace Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) :
    functionFieldMap f = functionFieldMap g := by
  subst g
  rfl

/-- Pullback of an equivariant dominant morphism commutes with the induced actions
on function fields. -/
theorem functionFieldMap_equivariant {Y : Scheme.{u}} [IrreducibleSpace Y]
    (ρ : M →* Aut X) (σ : M →* Aut Y) (f : X ⟶ Y) [IsDominant f]
    (h : ∀ m, (ρ m).hom ≫ f = f ≫ (σ m).hom) (m : M) (a : Y.functionField) :
    letI := functionFieldAction ρ
    letI := functionFieldAction σ
    functionFieldMap f (m • a) = m • functionFieldMap f a := by
  change ((functionFieldMap f).comp (functionFieldMap (σ m).inv)) a =
    ((functionFieldMap (ρ m).inv).comp (functionFieldMap f)) a
  rw [← functionFieldMap_comp, ← functionFieldMap_comp]
  exact congrArg (fun k : Y.functionField →+* X.functionField ↦ k a)
    (functionFieldMap_congr (aut_inv_natural (ρ m) (σ m) f (h m))).symm

end Irreducible

variable (K : Type u) [CommRing K] [X.Over (Spec (.of K))] [IsIntegral X]

/-- Inverse pullback by automorphisms over an affine base commutes with scalar
multiplication by the base ring. -/
theorem functionFieldAction_smulComm (ρ : M →* Aut (X.asOver (Spec (.of K)))) :
    let σ : M →* Aut X :=
      ((Over.forget (Spec (.of K))).mapAut (X.asOver (Spec (.of K)))).comp ρ
    letI := functionFieldAction σ
    SMulCommClass M K X.functionField := by
  let σ : M →* Aut X :=
    ((Over.forget (Spec (.of K))).mapAut (X.asOver (Spec (.of K)))).comp ρ
  let _ := functionFieldAction σ
  constructor
  intro m c a
  have : (σ m).inv.IsOver (Spec (.of K)) :=
    inferInstanceAs ((ρ m).inv.left.IsOver (Spec (.of K)))
  change functionFieldMap (σ m).inv (c • a) =
    c • functionFieldMap (σ m).inv a
  simp only [Algebra.smul_def, map_mul, functionFieldMap_algebraMap]

end

end GroupActions
