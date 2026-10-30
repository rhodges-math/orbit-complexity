import OrbitComplexity.GroupActions.Varieties.AffineFibres
import OrbitComplexity.GroupActions.Varieties.NormalizationDimension

/-! # Generic fibre dimension for integral affine schemes

An injective map of finitely generated domains over a field has a nonempty basic open
where the dimension of the source is the sum of the dimensions of the base and the fibre.
The proof spreads a polynomial normalization of the generic fibre.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

universe u

/-- A dominant morphism of integral affine schemes has the dimension formula on a
nonempty basic open of its base. -/
theorem exists_basicOpen_dim_add (K R A : Type u) [Field K] [CommRing R] [CommRing A]
    [IsDomain R] [IsDomain A] [Algebra K R] [Algebra K A] [Algebra R A]
    [IsScalarTower K R A] [Algebra.FiniteType K R] [Algebra.FiniteType K A]
    (hinj : Function.Injective (algebraMap R A)) :
    ∃ r : R, r ≠ 0 ∧ ∀ p ∈ PrimeSpectrum.basicOpen r,
      ringKrullDim A = ringKrullDim R +
        topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber p) := by
  let M := nonZeroDivisors R
  let k := FractionRing R
  let B := Localization (Algebra.algebraMapSubmonoid A M)
  have hmap : Algebra.algebraMapSubmonoid A M ≤ nonZeroDivisors A := by
    rintro a ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    exact fun h ↦ nonZeroDivisors.ne_zero hr (hinj (h.trans (map_zero _).symm))
  have : IsDomain B := IsLocalization.isDomain_localization hmap
  let : Algebra k B := localizationAlgebra M A
  have : IsScalarTower R k B :=
    isScalarTower_localizationAlgebra (Rₘ := k) (Sₘ := B) M A
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType K R A
  have : Algebra.IsPushout R k A B :=
    Algebra.IsPushout.symm (Algebra.isPushout_of_isLocalization M k A B)
  have : Algebra.FiniteType k B := Algebra.FiniteType.of_surjective
    (Algebra.IsPushout.equiv R k A B).toAlgHom (Algebra.IsPushout.equiv R k A B).surjective
  obtain ⟨n, x, m, hx, hi, hd⟩ :=
    exists_relative_normalization (A := A) (k := k) (B := B) M (IsFractionRing.injective R k)
  have hdim := ringKrullDim_eq_add_of_normalization K R A x
    (nonZeroDivisors.coe_ne_zero m) hinj hx hi
  rw [← hd] at hdim
  obtain ⟨m', hm'⟩ := exists_basicOpen_fibre_dim (A := A) (k := k) (B := B) M
    (IsFractionRing.injective R k)
  refine ⟨m', nonZeroDivisors.coe_ne_zero m', ?_⟩
  intro p hp
  rw [hm' p hp]
  exact hdim

end GroupActions
