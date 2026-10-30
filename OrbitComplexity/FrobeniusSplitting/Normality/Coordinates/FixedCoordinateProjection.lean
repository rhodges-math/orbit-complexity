import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateCocone

/-! # Projection equations in the fixed coordinate cocone -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem preimage_intersection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens) (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
    f ⁻¹ᵁ (intersectionOpens U).obj s =
      (intersectionOpens (fun i ↦ f ⁻¹ᵁ U i)).obj s := by
  change f ⁻¹ᵁ (⨅ i ∈ s.unop.val, U i) = ⨅ i ∈ s.unop.val, f ⁻¹ᵁ U i
  rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
  exact map_finset_inf f.base.frameHom _ _

private def openCocone {J : Type u} [Category.{u} J] (Y : Scheme.{u})
    (V : J ⥤ Y.Opens) : Cocone (V ⋙ Y.restrictFunctor ⋙ Over.forget Y) where
  pt := Y
  ι :=
    { app := fun s ↦ (V.obj s).ι
      naturality := by
        intro s t f
        change Y.homOfLE (leOfHom (V.map f)) ≫ (V.obj t).ι = (V.obj s).ι ≫ 𝟙 Y
        rw [Scheme.homOfLE_ι, Category.comp_id] }

private def openCocone_isColimit {Y : Scheme.{u}} {I : Type u}
    (V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Y.Opens)
    (U : I → Y.Opens) (hV : V = intersectionOpens U) (hcover : (⨆ i, U i) = ⊤) :
    IsColimit (openCocone Y V) := by
  subst V
  exact intersectionCoverIsColimit U hcover

/-- The prescribed coordinate extension has the prior pullback as its colimit,
with the section projection equation retained before any comparison. -/
theorem exists_fixed_coordinate_projection {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    {I : Type u} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) :
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let baseR := pullback.snd base sr
    let qR := pullback.fst base sr
    let B := intersectionOpens U
    let V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens :=
      { obj := fun s ↦ qR ⁻¹ᵁ B.obj s
        map := fun f ↦ homOfLE (qR.preimage_mono (leOfHom (B.map f))) }
    let E := V ⋙ YR.restrictFunctor ⋙ Over.map baseR
    let C := (E ⋙ algΓ (.of R)).unop
    let M := intersectionCoordinates base (intersectionOpens U)
    let N := fixedFibreDiagram (R := R) (M := R) M
    let v : ∀ s, M.obj s →+* C.obj s := fun s ↦ (qR ∣_ B.obj (.op s)).appTop.hom
    ∃ (hE : ∀ s, IsAffine (E.obj s).left)
      (d : N ≅ C) (cG : Cocone (N.op ⋙ algSpec (.of R))),
      (∀ s r x, (d.hom.app s).hom (r ⊗ₜ[S] x) =
        algebraMap R (C.obj s) r * v s x) ∧
      ∃ hpt : cG.pt = Over.mk baseR,
        Nonempty (IsColimit cG) ∧
        ∀ s, (cG.ι.app s ≫ eqToHom hpt).left =
          Spec.map (CommRingCat.ofHom (d.inv.app s.unop).hom.toRingHom) ≫
            (by letI := hE; exact ((coordinateDiagramIso (.of R) E).inv.app s).left) ≫
              (V.obj s).ι := by
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let YR := pullback base sr
  let baseR := pullback.snd base sr
  let qR := pullback.fst base sr
  let B := intersectionOpens U
  let V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens :=
    { obj := fun s ↦ qR ⁻¹ᵁ B.obj s
      map := fun f ↦ homOfLE (qR.preimage_mono (leOfHom (B.map f))) }
  let E := V ⋙ YR.restrictFunctor ⋙ Over.map baseR
  let C := (E ⋙ algΓ (.of R)).unop
  let M := intersectionCoordinates base (intersectionOpens U)
  let N := fixedFibreDiagram (R := R) (M := R) M
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  have hE (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj s).left := by
    have : IsAffine (B.obj s).toScheme := intersectionOpens_affine U hU s
    exact IsAffine.of_isPullback
      ((isPullback_morphismRestrict qR (B.obj s)).paste_vert
        (IsPullback.of_hasPullback base sr))
  let (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj s).left := hE s
  obtain ⟨e, he, hen⟩ := prior_intersection_coordinates base baseR qR
    (IsPullback.of_hasPullback base sr) U hU
  let d : N ≅ C := NatIso.ofComponents (fun s ↦ CommAlgCat.isoMk (e s)) (by
    intro s t f
    apply CommAlgCat.hom_ext
    exact hen s t f)
  let cE : Cocone E :=
    { pt := Over.mk baseR
      ι :=
        { app := fun s ↦ Over.homMk ((V.obj s).ι) rfl
          naturality := by
            intro s t f
            ext1
            change YR.homOfLE (leOfHom (V.map f)) ≫ (V.obj t).ι =
              (V.obj s).ι ≫ 𝟙 YR
            rw [Scheme.homOfLE_ι, Category.comp_id] } }
  let UR := fun i ↦ qR ⁻¹ᵁ U i
  have hV : V = intersectionOpens UR :=
    CategoryTheory.Functor.ext (fun s ↦ preimage_intersection qR U s)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hcoverR : (⨆ i, UR i) = ⊤ :=
    (TopologicalSpace.Opens.map_iSup qR.base U).symm.trans
      ((congrArg (fun V : Y.Opens ↦ qR ⁻¹ᵁ V) hcover).trans
        (TopologicalSpace.Opens.map_top qR.base))
  have hE0 : IsColimit ((Over.forget (Spec (.of R))).mapCocone cE) := by
    change IsColimit (openCocone YR V)
    exact openCocone_isColimit V UR hV hcoverR
  have hcE : IsColimit cE := isColimitOfReflects (Over.forget (Spec (.of R))) hE0
  let β := coordinateDiagramIso (.of R) E
  let cC := (Cocone.precompose β.inv).obj cE
  have hcC : IsColimit cC := (IsColimit.precomposeInvEquiv β _).symm hcE
  let α := Functor.isoWhiskerRight (NatIso.op d).symm (algSpec (.of R))
  let cG := (Cocone.precompose α.hom).obj cC
  refine ⟨hE, d, cG, he, rfl,
    ⟨(IsColimit.precomposeHomEquiv α cC).symm hcC⟩, ?_⟩
  intro s
  exact Category.comp_id _

end FrobeniusSplitting
