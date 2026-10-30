import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateCocone
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionSquares
import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers

/-! # Open gluing data for the prescribed coordinate diagram -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace FrobeniusSplitting

/-- A coordinate presentation of the affine intersections retains open arrows
and the union refinements needed for scheme gluing. -/
theorem coordinate_diagram_opens {R : Type u} [CommRing R] {Y : Scheme.{u}}
    [Y.IsSeparated] (base : Y ⟶ Spec (.of R)) {I : Type u}
    (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (d : N ≅ intersectionCoordinates base (intersectionOpens U)) :
    (∀ (s t) (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))) ∧
    ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := by
  let D := intersectionOpens U ⋙ Y.restrictFunctor ⋙ Over.map base
  have (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (D.obj s).left :=
    intersectionOpens_affine U hU s
  let A := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let B := (intersectionCoordinates base (intersectionOpens U)).op ⋙ algSpec (.of R) ⋙
    Over.forget (Spec (.of R))
  let e : A ≅ B := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (NatIso.op d).symm (algSpec (.of R))) (Over.forget _)
  have hopenB {s t} (f : s ⟶ t) : IsOpenImmersion (B.map f) := by
    exact coordinateMaps_open (.of R) D (fun _ _ f ↦ by
      change IsOpenImmersion (Y.homOfLE (leOfHom ((intersectionOpens U).map f)))
      infer_instance) f
  have hopenA {s t} (f : s ⟶ t) : IsOpenImmersion (A.map f) := by
    let E : Arrow.mk (A.map f) ≅ Arrow.mk (B.map f) :=
      Arrow.isoMk (e.app s) (e.app t) (e.hom.naturality f).symm
    exact (MorphismProperty.arrow_mk_iso_iff (@IsOpenImmersion) E).mpr (hopenB f)
  refine ⟨fun s t f ↦ hopenA f.op, ?_⟩
  apply locallyDirected_of_pullbacks A
  intro s t r fi fj
  obtain ⟨l, gi, gj, hp⟩ := intersectionCoordinates_refine base U hU s t r fi fj
  have H : IsPullback (B.map gi) (B.map gj) (B.map fi) (B.map fj) :=
    (isPushout_iff_spec_pullback _ _ _ _).mp hp
  refine ⟨l, gi, gj, ?_⟩
  exact H.of_iso (e.app l).symm (e.app s).symm (e.app t).symm (e.app r).symm
    (e.inv.naturality gi) (e.inv.naturality gj)
    (e.inv.naturality fi) (e.inv.naturality fj)

end FrobeniusSplitting
