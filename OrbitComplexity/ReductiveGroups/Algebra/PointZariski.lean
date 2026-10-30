import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Point Zariski

The Zariski topology on the `K`-points `A →ₐ[K] K` of a `K`-algebra
`A`, induced from `PrimeSpectrum A` through kernels. Its closed sets are
exactly the common zero loci of subsets of `A`; algebra maps induce
continuous maps on points; and the closure of a set of points is the zero
locus of the functions vanishing on it. -/

namespace ReductiveGroups

open Topology

variable (K : Type*) {A A' : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing A'] [Algebra K A']

/-- The common zero locus of `S ⊆ A` among the `K`-points of `A`. -/
def pointZeroLocus (S : Set A) : Set (A →ₐ[K] K) :=
  {φ | ∀ f ∈ S, φ f = 0}

variable {K}

/-- The kernel of a `K`-point `φ : A →ₐ[K] K`, as a point of `PrimeSpectrum A`. -/
def pointZariskiPrime (φ : A →ₐ[K] K) : PrimeSpectrum A :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩

/-- The Zariski topology on the `K`-points of `A`: the topology induced from
`PrimeSpectrum A` along `φ ↦ ker φ`. It is deliberately not an instance. -/
@[instance_reducible] def pointZariskiTopology : TopologicalSpace (A →ₐ[K] K) :=
  TopologicalSpace.induced pointZariskiPrime inferInstance

/-- The preimage of `PrimeSpectrum.zeroLocus S` under `φ ↦ ker φ` is the
point zero locus of `S`. -/
theorem pointZariskiPrime_preimage_zeroLocus (S : Set A) :
    (pointZariskiPrime (K := K)) ⁻¹' PrimeSpectrum.zeroLocus S = pointZeroLocus K S := by
  ext φ
  simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, pointZeroLocus,
    Set.mem_ofPred_eq, Set.subset_def]
  rfl

/-- A subset of `K`-points is closed for `pointZariskiTopology` if and only if
it is the point zero locus of some subset of `A`. -/
theorem pointZariski_isClosed_iff (s : Set (A →ₐ[K] K)) :
    IsClosed[pointZariskiTopology] s ↔ ∃ S : Set A, s = pointZeroLocus K S := by
  rw [pointZariskiTopology, isClosed_induced_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).mp ht
    exact ⟨S, pointZariskiPrime_preimage_zeroLocus S⟩
  · rintro ⟨S, rfl⟩
    exact ⟨PrimeSpectrum.zeroLocus S, PrimeSpectrum.isClosed_zeroLocus S,
      pointZariskiPrime_preimage_zeroLocus S⟩

/-- Every point zero locus is closed for `pointZariskiTopology`. -/
theorem pointZariski_isClosed_zeroLocus (S : Set A) :
    IsClosed[pointZariskiTopology] (pointZeroLocus K S) :=
  (pointZariski_isClosed_iff _).mpr ⟨S, rfl⟩

/-- Point zero loci are antitone in the subset of `A`. -/
theorem pointZeroLocus_anti {S T : Set A} (h : S ⊆ T) :
    pointZeroLocus K T ⊆ pointZeroLocus K S :=
  fun _ hφ f hf => hφ f (h hf)

/-- Pulling back along an algebra map `ψ : A →ₐ[K] A'` sends the point zero
locus of `S ⊆ A` to the point zero locus of `ψ '' S`. -/
theorem pointZeroLocus_preimage_comp (ψ : A →ₐ[K] A') (S : Set A) :
    (fun φ : A' →ₐ[K] K => φ.comp ψ) ⁻¹' pointZeroLocus K S =
      pointZeroLocus K (ψ '' S) := by
  ext φ
  simp [pointZeroLocus]

/-- An algebra map `ψ : A →ₐ[K] A'` induces a continuous map
`φ ↦ φ.comp ψ` on `K`-points for the point Zariski topologies. -/
theorem pointZariski_continuous_comp (ψ : A →ₐ[K] A') :
    Continuous[pointZariskiTopology, pointZariskiTopology]
      (fun φ : A' →ₐ[K] K => φ.comp ψ) := by
  let _ : TopologicalSpace (A →ₐ[K] K) := pointZariskiTopology
  let _ : TopologicalSpace (A' →ₐ[K] K) := pointZariskiTopology
  rw [continuous_iff_isClosed]
  intro s hs
  obtain ⟨S, rfl⟩ := (pointZariski_isClosed_iff s).mp hs
  rw [pointZeroLocus_preimage_comp]
  exact pointZariski_isClosed_zeroLocus _

/-- The closure of a set `s` of `K`-points for `pointZariskiTopology` is the
point zero locus of the functions vanishing at every point of `s`. -/
theorem pointZariski_closure_eq (s : Set (A →ₐ[K] K)) :
    closure[pointZariskiTopology] s =
      pointZeroLocus K {f : A | ∀ φ ∈ s, φ f = 0} := by
  let _ : TopologicalSpace (A →ₐ[K] K) := pointZariskiTopology
  apply le_antisymm
  · exact closure_minimal (fun φ hφ f hf => hf φ hφ) (pointZariski_isClosed_zeroLocus _)
  · obtain ⟨T, hT⟩ := (pointZariski_isClosed_iff (closure s)).mp isClosed_closure
    rw [hT]
    refine pointZeroLocus_anti fun f hf φ hφ => ?_
    have hφT : φ ∈ pointZeroLocus K T := hT ▸ subset_closure hφ
    exact hφT f hf

end ReductiveGroups
