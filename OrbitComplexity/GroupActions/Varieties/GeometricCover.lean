import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometric connectedness under point-surjective families

Geometric connectedness descends from a family of pullbacks whose base morphisms cover
all points. A point of a fibre product supplies a residue field over which the relevant
field probes can be compared.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace GroupActions

noncomputable section

universe u v

/-- Geometric connectedness descends along a family covering all target points. -/
theorem geometricallyConnected_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type v} (Z : ι → Scheme.{u}) (c : ∀ i, Z i ⟶ Y)
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (c i))
    (hlocal : ∀ i, GeometricallyConnected (pullback.snd f (c i))) :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ y
  obtain ⟨i, z, hz⟩ := hcover (y (IsLocalRing.closedPoint L))
  obtain ⟨p, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := c i) (g := y) z (IsLocalRing.closedPoint L) hz
  let r := (pullback (c i) y).fromSpecResidueField p
  let t := r ≫ pullback.fst (c i) y
  let q := r ≫ pullback.snd (c i) y
  have ht : t ≫ c i = q ≫ y := by
    dsimp only [t, q]
    simp only [Category.assoc, pullback.condition]
  have hc : ConnectedSpace (pullback (pullback.snd f (c i)) t : Scheme) :=
    pullback_of_geometrically (hlocal i).geometrically_connectedSpace
      ((pullback (c i) y).residueField p) t
  let e := pullbackLeftPullbackSndIso f (c i) t ≪≫ pullback.congrHom rfl ht
  have hq : ConnectedSpace (pullback f (q ≫ y) : Scheme) :=
    e.hom.homeomorph.connectedSpace_iff.mp hc
  let e' := pullbackLeftPullbackSndIso f y q
  let : ConnectedSpace (pullback (pullback.snd f y) q : Scheme) :=
    e'.hom.homeomorph.connectedSpace_iff.mpr hq
  exact (pullback.fst (pullback.snd f y) q).surjective.connectedSpace
    (pullback.fst (pullback.snd f y) q).continuous

end

end GroupActions
