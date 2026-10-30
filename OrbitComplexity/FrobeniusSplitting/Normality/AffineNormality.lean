import OrbitComplexity.FrobeniusSplitting.Normality.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Batteries.Tactic.Lint

/-! # Normal affine section rings

Domain and integrally closed stalks on an irreducible scheme give normal affine
section rings, with the zero ring retained for empty affine open subsets.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FrobeniusSplitting

universe u

/-- An affine open in an irreducible scheme with domain and integrally closed
stalks has either the zero ring or an integrally closed domain of sections. -/
theorem normal_sections_or_subsingleton {X : Scheme.{u}} [IrreducibleSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Subsingleton Γ(X, U) ∨ (IsDomain Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U)) := by
  classical
  let (x : X) : IsDomain (X.presheaf.stalk x) := (h x).1
  let : IsReduced X := isReduced_of_isReduced_stalk X
  let : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  rcases subsingleton_or_nontrivial Γ(X, U) with hzero | hnonzero
  · exact Or.inl hzero
  · let : Nontrivial Γ(X, U) := hnonzero
    let : Nonempty (Spec Γ(X, U)) := inferInstance
    let : Nonempty U := ⟨hU.isoSpec.inv (Classical.choice inferInstance)⟩
    let : IsDomain Γ(X, U) := IsIntegral.component_integral U
    exact Or.inr ⟨inferInstance, isIntegrallyClosed_of_stalks hU (fun x => (h x.1).2)⟩

/-- Affine normality, including the zero-ring alternative for an empty chart,
transports through a prescribed equivalence with its coordinate ring. -/
theorem normal_coordinates_or_subsingleton {X : Scheme.{u}} [IrreducibleSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) {A : Type u} [CommRing A]
    (E : Γ(X, U) ≃+* A) :
    Subsingleton A ∨ (IsDomain A ∧ IsIntegrallyClosed A) := by
  rcases normal_sections_or_subsingleton h hU with hzero | ⟨hdomain, hnormal⟩
  · let : Subsingleton Γ(X, U) := hzero
    exact Or.inl E.surjective.subsingleton
  · let : IsDomain Γ(X, U) := hdomain
    let : IsIntegrallyClosed Γ(X, U) := hnormal
    let : IsDomain A := (MulEquiv.isDomain_iff E.toMulEquiv).mp hdomain
    exact Or.inr ⟨inferInstance, IsIntegrallyClosed.of_equiv E⟩

end FrobeniusSplitting
