import OrbitComplexity.GroupActions.Varieties.GenericAffineFibres
import OrbitComplexity.GroupActions.Varieties.FibreIsomorphisms
import Mathlib.AlgebraicGeometry.Properties

/-! # Generic fibre dimension for affine schemes over a field

The affine ring dimension formula is invariant under the canonical isomorphisms between
affine schemes and the spectra of their global sections. This gives the generic fibre
formula for affine schemes with arbitrary presentations over a field.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

universe u

/-- A dominant morphism between integral affine schemes over a field satisfies the
dimension formula over a nonempty open part of its base. -/
theorem exists_open_dim_add_affine (K : Type u) [Field K] {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ q = p) :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ ∀ y ∈ U,
      topologicalKrullDim X = topologicalKrullDim Y + topologicalKrullDim (f.fiber y) := by
  let R := Γ(Y, ⊤)
  let A := Γ(X, ⊤)
  obtain ⟨φR, hR⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ q)
  obtain ⟨φA, hA⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  let : Algebra K R := φR.hom.toAlgebra
  let : Algebra K A := φA.hom.toAlgebra
  let : Algebra R A := f.appTop.hom.toAlgebra
  have hcomm : φA = φR ≫ f.appTop := by
    apply Spec.map_injective
    rw [Spec.map_comp, hA, hR, ← Category.assoc, Scheme.isoSpec_inv_naturality,
      Category.assoc, hf]
  have : IsScalarTower K R A := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hcomm)
  have hftR : LocallyOfFiniteType (Spec.map φR) := by rw [hR]; infer_instance
  have hftA : LocallyOfFiniteType (Spec.map φA) := by rw [hA]; infer_instance
  have : Algebra.FiniteType K R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φR)).mp hftR
  have : Algebra.FiniteType K A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φA)).mp hftA
  have : IsDominant (X.isoSpec.hom ≫ Spec.map f.appTop) := by
    rw [Scheme.isoSpec_hom_naturality]
    infer_instance
  have : IsDominant (Spec.map f.appTop) := IsDominant.of_comp X.isoSpec.hom _
  have hinj : Function.Injective (algebraMap R A) := by
    apply (RingHom.injective_iff_ker_eq_bot (algebraMap R A)).mpr
    apply le_bot_iff.mp
    have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f.appTop.hom).mp
      (Spec.map f.appTop).denseRange
    rw [nilradical_eq_zero] at hker
    change RingHom.ker f.appTop.hom ≤ 0
    exact hker
  obtain ⟨r, hr, hd⟩ := exists_basicOpen_dim_add K R A hinj
  let U : Y.Opens := Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  refine ⟨U, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := Y.isoSpec.hom.homeomorph.surjective
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
    refine ⟨y, ?_⟩
    change Y.isoSpec.hom.homeomorph y ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
    rw [hy]
    exact (PrimeSpectrum.mem_basicOpen r ⟨⊥, inferInstance⟩).mpr hr
  · intro y hy
    have hxy : topologicalKrullDim X = ringKrullDim A :=
      X.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
    have hyy : topologicalKrullDim Y = ringKrullDim R :=
      Y.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
    have h := hd (Y.isoSpec.hom y) hy
    rw [← hxy, ← hyy] at h
    change topologicalKrullDim X = topologicalKrullDim Y +
      topologicalKrullDim ((Spec.map f.appTop).fiber (Y.isoSpec.hom y)) at h
    rw [← fibre_dim_of_iso f (Spec.map f.appTop) X.isoSpec Y.isoSpec
      (Scheme.isoSpec_hom_naturality f) y] at h
    exact h

end GroupActions
