import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarAffineCoframes
import Batteries.Tactic.Lint

/-! # Coframes on scalar affine charts

The retained tensor-chart coframe is transported to the corresponding
chart of the scalar cover. Its field comparison is obtained by composing
the two prescribed comparison squares of the original line module.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem inverse_chart {C : Type u} [Category C] {A B Y YT : C}
    (I : A ≅ B) (j : A ⟶ Y) (f : B ⟶ YT) (q : YT ⟶ Y)
    (h : I.hom ≫ f ≫ q = j) : I.inv ≫ j = f ≫ q := by
  rw [← h]
  simp only [← Category.assoc, I.inv_hom_id, Category.id_comp]

private theorem inverse_field {C : Type u} [Category C] {A B P : C}
    (I : A ≅ B) (v : P ⟶ A) (u : P ⟶ B) (h : v ≫ I.hom = u) :
    u ≫ I.inv = v := by
  rw [← h]
  simp only [Category.assoc, I.hom_inv_id, Category.comp_id]

/-- Transport the retained coframe to the scalar-cover chart and derive
its comparison with the same field coframe on the original line. -/
theorem exists_scalar_chart_coframe {Y YT YK B BT P : Scheme.{u}}
    (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y)
    (hbase : n ≫ q = m)
    (j : B ⟶ Y) (f : BT ⟶ YT) (a : P ⟶ YK)
    (v : P ⟶ B) (u : P ⟶ BT) (I : B ≅ BT)
    (hold : I.hom ≫ f ≫ q = j) (hfield : v ≫ I.hom = u)
    (hsquare : u ≫ f = a ≫ n) (htotal : v ≫ j = a ≫ m)
    (L : Y.Modules) (E : (Scheme.Modules.pullback j).obj L ≅ unitModule B)
    (FK : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback m).obj L) ≅
      unitModule P)
    (hcompare : squareFrameIso m a j v htotal L E = FK) :
    ∃ ET : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback q).obj L) ≅
        unitModule BT,
      squareFrameIso n a f u hsquare ((Scheme.Modules.pullback q).obj L) ET =
        (Scheme.Modules.pullback a).mapIso
          ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ FK := by
  have hchart : u ≫ I.inv = v := inverse_field I v u hfield
  have hmodel : I.inv ≫ j = f ≫ q := inverse_chart I j f q hold
  let ET := squareFrameIso q f j I.inv hmodel L E
  refine ⟨ET, ?_⟩
  exact (squareFrameIso_stack_eq q n a f j u I.inv m v hbase hchart hsquare hmodel
    htotal L E).trans
      (congrArg (fun F => (Scheme.Modules.pullback a).mapIso
        ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ F) hcompare)

end SchubertGeometry.RetainedCharacter
