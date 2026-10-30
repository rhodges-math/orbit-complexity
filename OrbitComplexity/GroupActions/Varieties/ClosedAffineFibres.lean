import OrbitComplexity.GroupActions.Varieties.ClosedFibreAlgebra
import OrbitComplexity.GroupActions.Varieties.AffineSchemeFibres

/-! # Closed-point fibre bounds on affine schemes

The global sections of affine schemes turn a closed source point into a maximal ideal.
The height bound for its algebraic fibre transfers through the canonical affine
isomorphisms to a lower bound for the dimension of the scheme fibre.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

universe u

/-- A fibre under a closed point of an integral affine source has the dimension lower bound. -/
theorem dim_le_add_fiber_affine (K : Type u) [Field K] {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsIntegral X]
    (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (f : X ⟶ Y)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDim X ≤ topologicalKrullDim Y + topologicalKrullDim (f.fiber (f x)) := by
  let R := Γ(Y, ⊤)
  let A := Γ(X, ⊤)
  obtain ⟨φR, hR⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ q)
  obtain ⟨φA, hA⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  let : Algebra K R := φR.hom.toAlgebra
  let : Algebra K A := φA.hom.toAlgebra
  let : Algebra R A := f.appTop.hom.toAlgebra
  have hftR : LocallyOfFiniteType (Spec.map φR) := by rw [hR]; infer_instance
  have hftA : LocallyOfFiniteType (Spec.map φA) := by rw [hA]; infer_instance
  have : Algebra.FiniteType K R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φR)).mp hftR
  have : Algebra.FiniteType K A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φA)).mp hftA
  let P : PrimeSpectrum A := X.isoSpec.hom x
  have hP : IsClosed ({P} : Set (PrimeSpectrum A)) := by
    change IsClosed ({X.isoSpec.hom x} : Set (Spec A))
    simpa only [Set.image_singleton, Scheme.Hom.homeomorph_apply] using
      X.isoSpec.hom.homeomorph.isClosedMap _ hx
  have : P.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp hP
  have h := ringKrullDim_le_add_fiber (K := K) R A P.asIdeal
  have hxy : topologicalKrullDim X = ringKrullDim A :=
    X.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
  have hyy : topologicalKrullDim Y = ringKrullDim R :=
    Y.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
  have he : (PrimeSpectrum.comap f.appTop.hom) P = Y.isoSpec.hom (f x) := by
    exact congrArg (fun m : X ⟶ Spec (.of R) ↦ m x)
      (Scheme.isoSpec_hom_naturality f)
  rw [← hxy, ← hyy] at h
  have hfib := spec_fibre_dim R A (PrimeSpectrum.comap f.appTop.hom P)
  change topologicalKrullDim ((Spec.map f.appTop).fiber _) = _ at hfib
  change topologicalKrullDim X ≤ topologicalKrullDim Y +
    ringKrullDim ((PrimeSpectrum.comap f.appTop.hom P).asIdeal.Fiber A) at h
  rw [← hfib, he, ← fibre_dim_of_iso f (Spec.map f.appTop) X.isoSpec Y.isoSpec
    (Scheme.isoSpec_hom_naturality f) (f x)] at h
  exact h

end GroupActions
