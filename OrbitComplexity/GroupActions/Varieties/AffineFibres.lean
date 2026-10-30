import OrbitComplexity.GroupActions.Varieties.ScalarFibres
import Mathlib.AlgebraicGeometry.Fiber

/-! # Generic dimensions of affine scheme fibres

Scheme fibres of an affine morphism have the Krull dimensions of their residue-field
tensor algebras. Relative polynomial normalization makes this dimension constant on one
basic open of the base.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

universe u

/-- The dimension of an affine scheme fibre equals that of its residue-field tensor algebra. -/
theorem spec_fibre_dim (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber p) =
      ringKrullDim (p.asIdeal.Fiber A) := by
  let e := ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiberHomeo p).trans
    (PrimeSpectrum.preimageHomeomorphFiber R A p)
  exact e.isHomeomorph.topologicalKrullDim_eq.trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

/-- An affine finite-type map has constant generic fibre dimension on one basic open. -/
theorem exists_basicOpen_fibre_dim {R A k B : Type u} [CommRing R] [CommRing A]
    [Field k] [CommRing B] [Algebra R A] [Algebra R k] [Algebra A B] [Algebra R B]
    [Algebra k B] [IsScalarTower R A B] [IsScalarTower R k B] (M : Submonoid R)
    [IsLocalization M k] [IsLocalization (Algebra.algebraMapSubmonoid A M) B]
    [Nontrivial B] [Algebra.FiniteType k B] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R k)) :
    ∃ m : M, ∀ p ∈ PrimeSpectrum.basicOpen (m : R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber p) =
        ringKrullDim B := by
  obtain ⟨m, hm⟩ := exists_field_fibre_dim (A := A) (k := k) (B := B) M hinj
  refine ⟨m, ?_⟩
  intro p hp
  rw [spec_fibre_dim]
  apply hm p.asIdeal.ResidueField
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  exact hp (Ideal.algebraMap_residueField_eq_zero.mp hzero)

end GroupActions
