import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalDiagrams

/-! # A generator square inferred from its given unit comparison -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory
universe v u v' u'

/-- Infer the unit objects and morphisms from the unit comparison before specializing a generator.
  -/
theorem unitGenerator_square {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    {F : C ⥤ C} {H : C ⥤ D} {K : D ⥤ D} {N : F ⋙ H ⟶ H ⋙ K}
    {O : C} {A : D} {r : H.obj O ⟶ A} {ua : F.obj O ⟶ O} {uf : K.obj A ⟶ A}
    (hu : N.app O ≫ K.map r ≫ uf = H.map ua ≫ r)
    {M : C} (v : H.obj M ⟶ A) (s t : O ⟶ M) (x y : A ⟶ A)
    (hs : H.map s ≫ v = r ≫ x) (ht : H.map t ≫ v = r ≫ y)
    (hx : K.map x ≫ uf = uf ≫ y) :
    H.map (F.map s) ≫ N.app M ≫ K.map v ≫ uf = H.map (ua ≫ t) ≫ v :=
  naturalGenerator_square F H K N r ua uf v s t x y hs ht hu hx

end SchubertGeometry.ProjectiveLine
