import OrbitComplexity.GroupActions.Actions.Orbits
import OrbitComplexity.GroupActions.Varieties.Images
import OrbitComplexity.GroupActions.Varieties.ClosedPoints
import OrbitComplexity.GroupActions.Varieties.LocallyClosedImages

/-! # Local closedness of orbits

Constructibility gives a nonempty open part of the scheme closure of an orbit. Translation
then gives local closedness at each rational point of the orbit.

## Main results

* `GroupActions.orbit_locallyClosed`: rational-point orbits of a group variety
  are locally closed.
* `GroupActions.orbitImage_locallyClosed`: the scheme image of an orbit morphism is locally
  closed.

## References

* M. Brion, *Introduction to actions of algebraic groups*, Luminy lecture notes (2009),
  Proposition 1.11.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

omit [IsAlgClosed K] in
private theorem preimage_orbit_translation (h : H.points) (x : X.points) :
    Variety.mapPoints (Variety.translateMorphism H X h) ⁻¹' MulAction.orbit H.points x =
      MulAction.orbit H.points x := by
  ext y
  simp only [Set.mem_preimage, Variety.mapPoints_translateMorphism]
  constructor
  · intro hy
    simpa only [inv_smul_smul] using MulAction.mem_orbit_of_mem_orbit h⁻¹ hy
  · exact MulAction.mem_orbit_of_mem_orbit h

/-- Orbits of a group variety are locally closed among rational points. -/
theorem orbit_locallyClosed (x : X.points) :
    IsLocallyClosed (MulAction.orbit H.points x) := by
  have : Nonempty H.scheme := ⟨H.pointMap 1⟩
  let f := Variety.orbitMorphism H X x
  obtain ⟨U, hU, hUne, hUrange⟩ := Variety.exists_open_inter_range f
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints hUne
    (hU.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  obtain ⟨y, hy⟩ := X.pointsEquivClosedPoints.surjective ⟨p, hpc⟩
  have hyeval : X.pointMap y = p := congrArg Subtype.val hy
  have hyimage : X.pointMap y ∈ Set.range (f.left : H.scheme → X.scheme) := by
    rw [hyeval]
    exact hUrange hp
  obtain ⟨h, hh⟩ := Variety.exists_mapPoints_eq f y hyimage
  have hyorbit : y ∈ MulAction.orbit H.points x := by
    rw [← hh]
    rw [show f = Variety.orbitMorphism H X x from rfl, Variety.mapPoints_orbitMorphism]
    exact MulAction.mem_orbit x h
  have hlocal : IsLocallyClosedAt (MulAction.orbit H.points x) y := by
    apply isLocallyClosedAt_iff_exists_inter_closure_subset.mpr
    refine ⟨X.pointMap ⁻¹' U, (hU.preimage X.continuous_pointMap).mem_nhds ?_, ?_⟩
    · change X.pointMap y ∈ U
      rw [hyeval]
      exact hp.1
    · intro z hz
      have hzclosure : X.pointMap z ∈ closure (Set.range (f.left : H.scheme → X.scheme)) := by
        rw [← orbitClosure_eq H X x]
        change X.pointMap z ∈ X.pointClosure (MulAction.orbit H.points x)
        have heq := X.isEmbedding_pointMap.closure_eq_preimage_closure_image
          (MulAction.orbit H.points x)
        rw [heq] at hz
        exact hz.2
      obtain ⟨k, hk⟩ := Variety.exists_mapPoints_eq f z (hUrange ⟨hz.1, hzclosure⟩)
      rw [← hk]
      rw [show f = Variety.orbitMorphism H X x from rfl, Variety.mapPoints_orbitMorphism]
      exact MulAction.mem_orbit x k
  apply isLocallyClosed_iff_isLocallyClosedAt.mpr
  intro z hz
  obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.mem_orbit_trans hyorbit (MulAction.mem_orbit_symm.mp hz))
  have hyz : Variety.mapPoints (Variety.translateMorphism H X k) z = y :=
    (Variety.mapPoints_translateMorphism H X k z).trans hk
  have hlocal' := (hyz.symm ▸ hlocal).preimage (Variety.continuous_mapPoints
    (Variety.translateMorphism H X k))
  simpa only [preimage_orbit_translation] using hlocal'

/-- The scheme image of an orbit morphism of a group variety is locally closed. -/
theorem orbitImage_locallyClosed (x : X.points) :
    IsLocallyClosed (Set.range ((Variety.orbitMorphism H X x).left : H.scheme → X.scheme)) := by
  apply Variety.isLocallyClosed_range
  rw [Variety.range_orbitMorphism]
  exact orbit_locallyClosed H X x

end

end GroupActions
