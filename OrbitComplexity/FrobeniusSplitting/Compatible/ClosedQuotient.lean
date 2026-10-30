import OrbitComplexity.FrobeniusSplitting.Compatible.Quotient
import OrbitComplexity.FrobeniusSplitting.Compatible.Schemes
import OrbitComplexity.FrobeniusSplitting.Splittings.Spec
import OrbitComplexity.FrobeniusSplitting.Splittings.Transport
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Batteries.Tactic.Lint

/-! # Splittings on affine closed subschemes

A splitting preserving the kernel of a surjective ring map induces a splitting
on its target. Applied to global sections of an affine closed immersion, this
gives a splitting on the closed subscheme.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u
namespace FrobeniusSplitting
namespace RingSplitting

/-- A splitting preserving a surjective homomorphism's kernel descends to its target. -/
def ofSurjective {R S : Type u} [CommRing R] [CommRing S] {p : ℕ}
    (splitting : RingSplitting R p) (f : R →+* S) (hf : Function.Surjective f)
    (hker : splitting.IsCompatible (RingHom.ker f)) : RingSplitting S p :=
  (splitting.quotient (RingHom.ker f) hker).transport
    (f.quotientKerEquivOfSurjective hf)

/-- The descended splitting commutes with the original surjective homomorphism. -/
theorem ofSurjective_map {R S : Type u} [CommRing R] [CommRing S] {p : ℕ}
    (splitting : RingSplitting R p) (f : R →+* S) (hf : Function.Surjective f)
    (hker : splitting.IsCompatible (RingHom.ker f)) (a : R) :
    splitting.ofSurjective f hf hker (f a) = f (splitting a) := by
  rw [ofSurjective, transport_apply,
    RingHom.quotientKerEquivOfSurjective_symm_apply, quotient_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end RingSplitting
namespace SchemeSplitting

private theorem affine_kernel {X Y : Scheme.{u}} [IsAffine X] {p : ℕ}
    (splitting : SchemeSplitting X p) (j : Y ⟶ X) [IsClosedImmersion j]
    (hker : splitting.IsCompatible j.ker) :
    (splitting.onOpen ⊤).IsCompatible (RingHom.ker j.appTop.hom) := by
  erw [← j.ker_apply ⟨⊤, isAffineOpen_top X⟩]
  exact hker ⟨⊤, isAffineOpen_top X⟩

/-- A compatible closed subscheme of an affine split scheme is split. -/
def closedAffine {X Y : Scheme.{u}} [IsAffine X] {p : ℕ}
    (splitting : SchemeSplitting X p) (j : Y ⟶ X) [IsClosedImmersion j]
    (hp : 0 < p) (hker : splitting.IsCompatible j.ker) : SchemeSplitting Y p := by
  letI : IsAffine Y := isAffine_of_isAffineHom j
  exact ((splitting.onOpen ⊤).ofSurjective j.appTop.hom
    (j.app_surjective ⊤ (isAffineOpen_top X))
    (affine_kernel splitting j hker)).toAffine hp

end SchemeSplitting
end FrobeniusSplitting
