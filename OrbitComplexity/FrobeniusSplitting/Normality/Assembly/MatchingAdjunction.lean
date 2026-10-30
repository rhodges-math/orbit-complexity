import Mathlib.CategoryTheory.Adjunction.Basic
import Batteries.Tactic.Lint

/-!
# Matching coordinates through an adjunction

A right adjoint preserves the joint monomorphism of matching coordinates.
Coordinate comparisons and section comparisons can therefore be transported
through the adjunction without computing in the module objects.
-/

set_option autoImplicit false

open CategoryTheory

namespace FrobeniusSplitting.RetainedCharacter

universe u v w

/-- Jointly monomorphic coordinates remain jointly monomorphic after a right adjoint. -/
theorem adjoint_coordinate_ext {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {I : Type*} {N : D} (Q : I → D) (π : ∀ i : I, N ⟶ Q i)
    (hπ : ∀ {P : D} (f g : P ⟶ N), (∀ i : I, f ≫ π i = g ≫ π i) → f = g)
    {M : C} (f g : M ⟶ G.obj N)
    (hfg : ∀ i : I, f ≫ G.map (π i) = g ≫ G.map (π i)) : f = g := by
  apply (adj.homEquiv M N).symm.injective
  apply hπ
  intro i
  simpa only [adj.homEquiv_naturality_right_symm] using
    congrArg (adj.homEquiv M (Q i)).symm (hfg i)

/-- An equation for a pushed-forward coordinate gives the corresponding equation
for the adjoint transpose. -/
theorem adjoint_coordinate {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M : C} {N Q : D} (ψ : M ⟶ G.obj N) (π : N ⟶ Q)
    (f : M ⟶ G.obj Q) (h : ψ ≫ G.map π = f) :
    (adj.homEquiv M N).symm ψ ≫ π = (adj.homEquiv M Q).symm f :=
  (adj.homEquiv_naturality_right_symm ψ π).symm.trans
    (congrArg (adj.homEquiv M Q).symm h)

/-- A section equation for a right-adjoint morphism gives the section equation
for its transpose, using the specified isomorphism of unit objects. -/
theorem adjoint_section {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A M : C} {B N : D} (e : F.obj A ≅ B) (u : A ⟶ G.obj B)
    (hu : adj.homEquiv A B e.hom = u)
    (s : A ⟶ M) (t : B ⟶ N) (ψ : M ⟶ G.obj N)
    (h : s ≫ ψ = u ≫ G.map t) :
    e.inv ≫ F.map s ≫ (adj.homEquiv M N).symm ψ = t := by
  have hs : F.map s ≫ (adj.homEquiv M N).symm ψ = e.hom ≫ t := by
    apply (adj.homEquiv A N).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply, hu]
    exact h
  rw [hs, Iso.inv_hom_id_assoc]

end FrobeniusSplitting.RetainedCharacter
