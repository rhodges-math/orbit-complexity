import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Topology.KrullDimension

/-! # Fibre dimensions under isomorphisms

Isomorphisms of the source and base which commute with two morphisms identify their
scheme fibres as topological spaces. Their Krull dimensions consequently agree.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

/-- Commuting isomorphisms of the source and base give homeomorphic scheme fibres. -/
def fiberIsoHomeomorph {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (e : X ≅ X') (e' : Y ≅ Y') (h : e.hom ≫ g = f ≫ e'.hom) (y : Y) :
    f.fiber y ≃ₜ g.fiber (e'.hom y) := by
  refine (f.fiberHomeo y).trans ((e.hom.homeomorph.subtype ?_).trans
    (g.fiberHomeo (e'.hom y)).symm)
  intro x
  change f x = y ↔ g (e.hom x) = e'.hom y
  have hx : g (e.hom x) = e'.hom (f x) :=
    congrArg (fun m : X ⟶ Y' ↦ m x) h
  rw [hx]
  exact e'.hom.homeomorph.injective.eq_iff.symm

/-- Commuting isomorphisms of a morphism preserve the dimensions of corresponding fibres. -/
theorem fibre_dim_of_iso {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (e : X ≅ X') (e' : Y ≅ Y') (h : e.hom ≫ g = f ≫ e'.hom) (y : Y) :
    topologicalKrullDim (f.fiber y) = topologicalKrullDim (g.fiber (e'.hom y)) :=
  (fiberIsoHomeomorph f g e e' h y).isHomeomorph.topologicalKrullDim_eq

end

end GroupActions
