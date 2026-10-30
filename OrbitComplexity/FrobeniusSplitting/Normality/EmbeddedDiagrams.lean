import Batteries.Tactic.Lint
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# EmbeddedDiagrams

Arithmetic coefficient models and compatible chart comparisons.
-/

open CategoryTheory

namespace FrobeniusSplitting

universe u v w

/-- Injective coordinate embeddings reflect functor identities and composition laws
for compatible coefficient-algebra maps. -/
@[implicit_reducible]
def modelFunctor {C : Type v} [Category.{w} C] {R : Type u} [CommRing R]
    (M : C → Type u) [∀ i, CommRing (M i)] [∀ i, Algebra R (M i)]
    (D : C ⥤ CommRingCat.{u}) (maps : ∀ {i j}, (i ⟶ j) → M i →ₐ[R] M j)
    (q : ∀ i, M i →+* D.obj i) (hq : ∀ i, Function.Injective (q i))
    (hcomm : ∀ i j (f : i ⟶ j) z, q j (maps f z) = (D.map f).hom (q i z)) :
    C ⥤ CommAlgCat.{u} R :=
  { obj := fun i ↦ CommAlgCat.of R (M i)
    map := fun f ↦ CommAlgCat.ofHom (maps f)
    map_id := by
      intro i
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      apply hq i
      exact (hcomm i i (𝟙 i) z).trans (RingHom.congr_fun
        (congrArg (fun f : D.obj i ⟶ D.obj i ↦ f.hom) (D.map_id i)) (q i z))
    map_comp := by
      intro i j k f g
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      apply hq k
      calc
        q k (maps (f ≫ g) z) = (D.map (f ≫ g)).hom (q i z) := hcomm _ _ _ _
        _ = (D.map g).hom ((D.map f).hom (q i z)) := RingHom.congr_fun
          (congrArg (fun f : D.obj i ⟶ D.obj k ↦ f.hom) (D.map_comp f g)) _
        _ = (D.map g).hom (q j (maps f z)) := congrArg (D.map g).hom (hcomm _ _ _ _).symm
        _ = q k (maps g (maps f z)) := (hcomm _ _ _ _).symm }

end FrobeniusSplitting
