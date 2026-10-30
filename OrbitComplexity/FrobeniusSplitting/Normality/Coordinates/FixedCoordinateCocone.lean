import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorIntersectionCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams

/-! # The fixed coordinate diagram has the proper base change as its colimit -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem intersection_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens) (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
    f ⁻¹ᵁ (intersectionOpens U).obj s =
      (intersectionOpens (fun i ↦ f ⁻¹ᵁ U i)).obj s := by
  change f ⁻¹ᵁ (⨅ i ∈ s.unop.val, U i) = ⨅ i ∈ s.unop.val, f ⁻¹ᵁ U i
  rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
  exact map_finset_inf f.base.frameHom _ _

/-- The tensor extension of the chosen intersection diagram has the
proper prior scheme's coefficient pullback as its specified colimit. -/
theorem exists_fixed_coordinate_cocone {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    {I : Type u} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) :
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let baseR := pullback.snd base sr
    let qR := pullback.fst base sr
    let UR := fun i ↦ qR ⁻¹ᵁ U i
    letI : YR.IsSeparated := ⟨by rw [← terminal.comp_from baseR]; infer_instance⟩
    let M := intersectionCoordinates base (intersectionOpens U)
    let N := fixedFibreDiagram (R := R) (M := R) M
    ∃ (hUR : ∀ i, IsAffineOpen (UR i))
      (d : N ≅ intersectionCoordinates baseR (intersectionOpens UR))
      (cR : Cocone (N.op ⋙ algSpec (.of R))),
      ∃ hpt : cR.pt = Over.mk baseR, Nonempty (IsColimit cR) ∧
      ∀ s, cR.ι.app s ≫ eqToHom hpt =
        (algSpec (.of R)).map ((d.inv.app s.unop).op) ≫
          (intersectionCoordinateCocone baseR UR hUR).ι.app s := by
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let YR := pullback base sr
  let baseR := pullback.snd base sr
  let qR := pullback.fst base sr
  let UR := fun i ↦ qR ⁻¹ᵁ U i
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  have : YR.IsSeparated := ⟨by rw [← terminal.comp_from baseR]; infer_instance⟩
  have hUR (i : I) : IsAffineOpen (UR i) := by
    have : IsAffine (U i).toScheme := hU i
    exact IsAffine.of_isPullback
      ((isPullback_morphismRestrict qR (U i)).paste_vert (IsPullback.of_hasPullback base sr))
  have hcoverR : (⨆ i, UR i) = ⊤ := by
    change (⨆ i, (TopologicalSpace.Opens.map qR.base).obj (U i)) = ⊤
    exact (TopologicalSpace.Opens.map_iSup qR.base U).symm.trans
      ((congrArg (fun V : Y.Opens ↦ qR ⁻¹ᵁ V) hcover).trans
        (TopologicalSpace.Opens.map_top qR.base))
  let B := intersectionOpens U
  let V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens :=
    { obj := fun s ↦ qR ⁻¹ᵁ B.obj s
      map := fun f ↦ homOfLE (qR.preimage_mono (leOfHom (B.map f))) }
  have hV : V = intersectionOpens UR :=
    CategoryTheory.Functor.ext (fun s ↦ intersection_preimage qR U s)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
  obtain ⟨e, he, hen⟩ := prior_intersection_coordinates base baseR qR
    (IsPullback.of_hasPullback base sr) U hU
  let M := intersectionCoordinates base (intersectionOpens U)
  let N := fixedFibreDiagram (R := R) (M := R) M
  let F := ((V ⋙ YR.restrictFunctor ⋙ Over.map baseR) ⋙ algΓ (.of R)).unop
  have hF : F = intersectionCoordinates baseR (intersectionOpens UR) :=
    congrArg (fun D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens ↦
      ((D ⋙ YR.restrictFunctor ⋙ Over.map baseR) ⋙ algΓ (.of R)).unop) hV
  let d0 : N ≅ F := NatIso.ofComponents (fun s ↦ CommAlgCat.isoMk (e s)) (by
    intro s t f
    apply CommAlgCat.hom_ext
    exact hen s t f)
  let d : N ≅ intersectionCoordinates baseR (intersectionOpens UR) := d0 ≪≫ eqToIso hF
  let a := Functor.isoWhiskerRight (NatIso.op d).symm (algSpec (.of R))
  let cD := intersectionCoordinateCocone baseR UR hUR
  let cR := (Cocone.precompose a.hom).obj cD
  have hcD : IsColimit cD := coordinateCoconeIsColimit baseR UR hUR hcoverR
  refine ⟨hUR, d, cR, rfl, ⟨(IsColimit.precomposeHomEquiv a cD).symm hcD⟩, ?_⟩
  intro s
  exact Category.comp_id _

end FrobeniusSplitting
