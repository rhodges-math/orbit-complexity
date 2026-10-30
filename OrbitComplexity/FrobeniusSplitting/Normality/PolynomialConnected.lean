import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Topology.Connected.Basic

/-!
# Connected spectra from polynomial contractions

A polynomial homotopy from the identity to a field-valued point makes an
affine spectrum connected, including its nonclosed points and nilpotents.

For each prime ideal, specialize the polynomial homotopy to its residue field.
The image of that irreducible affine line contains both the chosen field point
and the original prime. Thus all primes lie in one connected component.

The proof uses generic ring-homomorphism equations before specializing to residue
fields. It does not identify a concrete polynomial spectrum with a scheme
pullback or compute inside a concrete localization.
-/

open AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

private theorem eval_map_comp
    {A : Type u} {F : Type v} [CommRing A] [CommRing F]
    (q : A →+* F) (α : A →+* Polynomial A) (t : A) :
    (Polynomial.evalRingHom (q t)).comp ((Polynomial.mapRingHom q).comp α) =
      q.comp ((Polynomial.evalRingHom t).comp α) := by
  apply RingHom.ext
  intro c
  exact Polynomial.eval_map_apply (f := q) (p := α c) t

private theorem eval_zero_map_comp
    {A : Type u} {F : Type v} [CommRing A] [CommRing F]
    (q : A →+* F) (α : A →+* Polynomial A) :
    (Polynomial.evalRingHom (0 : F)).comp ((Polynomial.mapRingHom q).comp α) =
      q.comp ((Polynomial.evalRingHom (0 : A)).comp α) := by
  simpa only [map_zero] using eval_map_comp q α (0 : A)

private theorem eval_one_map_comp
    {A : Type u} {F : Type v} [CommRing A] [CommRing F]
    (q : A →+* F) (α : A →+* Polynomial A) :
    (Polynomial.evalRingHom (1 : F)).comp ((Polynomial.mapRingHom q).comp α) =
      q.comp ((Polynomial.evalRingHom (1 : A)).comp α) := by
  simpa only [map_one] using eval_map_comp q α (1 : A)

private theorem comap_eval_eq
    {A : Type u} {F : Type v} [CommRing A] [Field F]
    (g : A →+* Polynomial F) (t : F) (p : PrimeSpectrum A)
    (h : RingHom.ker ((Polynomial.evalRingHom t).comp g) = p.asIdeal) :
    PrimeSpectrum.comap g
      (PrimeSpectrum.comap (Polynomial.evalRingHom t) (⊥ : PrimeSpectrum F)) = p := by
  apply PrimeSpectrum.ext
  exact h

/-- A polynomial homotopy from the identity to a point valued in a field
makes the entire prime spectrum connected. No reducedness, finite-type or
algebraic-closedness hypothesis is needed. -/
theorem primeSpectrum_connected_of_polynomial
    {K : Type u} {C : Type v} [Field K] [CommRing C]
    (i : K →+* C) (ε : C →+* K) (σ : C →+* Polynomial C)
    (h1 : ∀ c : C, (σ c).eval 1 = c)
    (h0 : ∀ c : C, (σ c).eval 0 = i (ε c)) :
    ConnectedSpace (PrimeSpectrum C) := by
  let anchor : PrimeSpectrum C := PrimeSpectrum.comap ε (⊥ : PrimeSpectrum K)
  have hσ1 : (Polynomial.evalRingHom (1 : C)).comp σ = RingHom.id C :=
    RingHom.ext h1
  have hσ0 : (Polynomial.evalRingHom (0 : C)).comp σ = i.comp ε :=
    RingHom.ext h0
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨anchor, Set.eq_univ_iff_forall.mpr ?_⟩
  intro p
  let F : Type v := p.asIdeal.ResidueField
  let q : C →+* F := algebraMap C F
  let g : C →+* Polynomial F := (Polynomial.mapRingHom q).comp σ
  have hg1 : (Polynomial.evalRingHom (1 : F)).comp g = q := by
    dsimp only [g]
    rw [eval_one_map_comp, hσ1, RingHom.comp_id]
  have hg0 : (Polynomial.evalRingHom (0 : F)).comp g = (q.comp i).comp ε := by
    dsimp only [g]
    rw [eval_zero_map_comp, hσ0]
    exact (RingHom.comp_assoc ε i q).symm
  have hk1 :
      RingHom.ker ((Polynomial.evalRingHom (1 : F)).comp g) = p.asIdeal := by
    rw [hg1]
    exact Ideal.ker_algebraMap_residueField p.asIdeal
  have hk0 :
      RingHom.ker ((Polynomial.evalRingHom (0 : F)).comp g) = anchor.asIdeal := by
    rw [hg0, RingHom.ker_comp_of_injective ε (q.comp i).injective]
    rfl
  have hzero :
      PrimeSpectrum.comap g
        (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : F))
          (⊥ : PrimeSpectrum F)) = anchor :=
    comap_eval_eq g 0 anchor hk0
  have hone :
      PrimeSpectrum.comap g
        (PrimeSpectrum.comap (Polynomial.evalRingHom (1 : F))
          (⊥ : PrimeSpectrum F)) = p :=
    comap_eval_eq g 1 p hk1
  let : IrreducibleSpace (PrimeSpectrum (Polynomial F)) := inferInstance
  have himage : _root_.IsPreconnected
      (PrimeSpectrum.comap g '' (Set.univ : Set (PrimeSpectrum (Polynomial F)))) :=
    isPreconnected_univ.image _ (PrimeSpectrum.continuous_comap g).continuousOn
  have hanchor : anchor ∈
      PrimeSpectrum.comap g '' (Set.univ : Set (PrimeSpectrum (Polynomial F))) :=
    ⟨PrimeSpectrum.comap (Polynomial.evalRingHom (0 : F)) (⊥ : PrimeSpectrum F),
      Set.mem_univ _, hzero⟩
  have hp : p ∈
      PrimeSpectrum.comap g '' (Set.univ : Set (PrimeSpectrum (Polynomial F))) :=
    ⟨PrimeSpectrum.comap (Polynomial.evalRingHom (1 : F)) (⊥ : PrimeSpectrum F),
      Set.mem_univ _, hone⟩
  exact himage.subset_connectedComponent hanchor hp

/-- A field-linear polynomial contraction makes the associated affine scheme
connected. The zero equation uses the specified field-valued origin map. -/
theorem spec_connected_of_polynomial
    {K : Type u} {C : Type v} [Field K] [CommRing C] [Algebra K C]
    (σ : C →ₐ[K] Polynomial C) (ε : C →ₐ[K] K)
    (h1 : ∀ c : C, (σ c).eval 1 = c)
    (h0 : ∀ c : C, (σ c).eval 0 = algebraMap K C (ε c)) :
    ConnectedSpace (Spec (.of C)) := by
  exact primeSpectrum_connected_of_polynomial
    (algebraMap K C) ε.toRingHom σ.toRingHom h1 h0

end FrobeniusSplitting
