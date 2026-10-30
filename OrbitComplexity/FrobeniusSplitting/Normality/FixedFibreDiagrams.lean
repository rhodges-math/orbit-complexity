import Batteries.Tactic.Lint
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# FixedFibreDiagrams

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

/-- Tensoring a fixed coefficient algebra with an integral fibre chart diagram gives
a diagram over the coefficient ring. -/
@[implicit_reducible]
def fixedFibreDiagram {J : Type v} [Category.{w} J]
    {S R M : Type u} [CommRing S] [CommRing R] [CommRing M]
    [Algebra S R] [Algebra R M] [Algebra S M] [IsScalarTower S R M]
    (G : J ⥤ CommAlgCat.{u} S) : J ⥤ CommAlgCat.{u} R where
  obj i := CommAlgCat.of R (M ⊗[S] G.obj i)
  map f := CommAlgCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R M) (G.map f).hom)
  map_id i := by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro m a
    change m ⊗ₜ[S] (G.map (𝟙 i)).hom a = m ⊗ₜ[S] a
    rw [G.map_id]
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro m a
    change m ⊗ₜ[S] (G.map (f ≫ g)).hom a =
      m ⊗ₜ[S] (G.map g).hom ((G.map f).hom a)
    rw [G.map_comp]
    rfl

end FrobeniusSplitting
