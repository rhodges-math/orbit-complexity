import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Generator squares for pullback and restriction -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory CategoryTheory.Limits
universe v u v' u'

/-- A natural pullback comparison carries a generator to its transformed scalar. -/
theorem naturalGenerator_square {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    (F : C ⥤ C) (H : C ⥤ D) (K : D ⥤ D) (N : F ⋙ H ⟶ H ⋙ K)
    {O M : C} {A : D} (r : H.obj O ⟶ A) (ua : F.obj O ⟶ O)
    (uf : K.obj A ⟶ A) (v : H.obj M ⟶ A) (s t : O ⟶ M)
    (x y : A ⟶ A)
    (hs : H.map s ≫ v = r ≫ x) (ht : H.map t ≫ v = r ≫ y)
    (hu : N.app O ≫ K.map r ≫ uf = H.map ua ≫ r)
    (hx : K.map x ≫ uf = uf ≫ y) :
    H.map (F.map s) ≫ N.app M ≫ K.map v ≫ uf = H.map (ua ≫ t) ≫ v := by
  have hn : H.map (F.map s) ≫ N.app M = N.app O ≫ K.map (H.map s) :=
    N.naturality s
  calc
    _ = (H.map (F.map s) ≫ N.app M) ≫ K.map v ≫ uf := by
      simp only [Category.assoc]
    _ = (N.app O ≫ K.map (H.map s)) ≫ K.map v ≫ uf :=
      congrArg (fun m => m ≫ K.map v ≫ uf) hn
    _ = N.app O ≫ K.map (H.map s ≫ v) ≫ uf := by
      simp only [Functor.map_comp, Category.assoc]
    _ = N.app O ≫ K.map (r ≫ x) ≫ uf := by rw [hs]
    _ = N.app O ≫ K.map r ≫ uf ≫ y := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hx]
    _ = (H.map ua ≫ r) ≫ y := by
      simpa only [Category.assoc] using congrArg (fun m => m ≫ y) hu
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using
        (congrArg (fun m => H.map ua ≫ m) ht).symm

/-- Adjunction carries a local commuting square to the global commuting square. -/
theorem adjunctionGenerator_square {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] {H : C ⥤ D} {P : D ⥤ C}
    (adj : H ⊣ P) {E M N : C} {A : D}
    (e : E ⟶ M) (g : E ⟶ N) (q : H.obj M ⟶ A) (i : H.obj N ⟶ A)
    (h : H.map e ≫ q = H.map g ≫ i) :
    e ≫ adj.homEquiv _ _ q = g ≫ adj.homEquiv _ _ i :=
  (adj.homEquiv_naturality_left e q).symm.trans
    ((congrArg (adj.homEquiv E A) h).trans (adj.homEquiv_naturality_left g i))

end SchubertGeometry.ProjectiveLine
