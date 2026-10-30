import OrbitComplexity.SchubertGeometry.LineBundles.Modules.UnitGenerator

/-! # Adjunction targets constructed before geometric specialization -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory
universe v u v' u'

/-- The adjoint chart target carries every section with the specified coefficient change. -/
theorem adjointGenerator_exists {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    {F : C ⥤ C} {H : C ⥤ D} {K : D ⥤ D} {P : D ⥤ C}
    {N : F ⋙ H ⟶ H ⋙ K} {O : C} {A : D}
    {r : H.obj O ⟶ A} {ua : F.obj O ⟶ O} {uf : K.obj A ⟶ A}
    (hu : N.app O ≫ K.map r ≫ uf = H.map ua ≫ r)
    (adj : H ⊣ P) {M : C} (v : H.obj M ⟶ A) :
    ∃ q : F.obj M ⟶ P.obj A,
      ∀ (s t : O ⟶ M) (x y : A ⟶ A),
        H.map s ≫ v = r ≫ x → H.map t ≫ v = r ≫ y →
        K.map x ≫ uf = uf ≫ y →
        F.map s ≫ q = (ua ≫ t) ≫ adj.homEquiv M A v := by
  refine ⟨adj.homEquiv (F.obj M) A (N.app M ≫ K.map v ≫ uf), ?_⟩
  intro s t x y hs ht hx
  exact adjunctionGenerator_square adj (F.map s) (ua ≫ t) _ v
    (unitGenerator_square hu v s t x y hs ht hx)

end SchubertGeometry.ProjectiveLine
