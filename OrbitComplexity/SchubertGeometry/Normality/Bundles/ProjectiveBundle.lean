import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveBundleData

/-! # Gluing projective-line diagrams over their specified base colimit -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions FrobeniusSplitting
noncomputable section
universe u
namespace SchubertGeometry

/-- projective-line components give proper smooth bundles with connected geometric fibres. -/
theorem exists_projective_bundle {J R : Type u} [Category.{u} J] [Quiver.IsThin J]
    [CommRing R] (N : J ⥤ CommAlgCat.{u} R)
    [∀ {j k} (f : j ⟶ k), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (hπ : π.Equifibered)
    (e : ∀ j, D.obj j ≅ projectiveScheme (N.obj j.unop) (ULift.{u} (Fin 2)))
    (he : ∀ j, π.app j = (e j).hom ≫
      projectiveToSpec (N.obj j.unop) (ULift.{u} (Fin 2)))
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG) :
    projectiveBundleSpec N D π cG := by
  let B := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let {j k : Jᵒᵖ} (f : j ⟶ k) : IsOpenImmersion (B.map f) :=
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)))
  let {j k : Jᵒᵖ} (f : j ⟶ k) : IsOpenImmersion (D.map f) := by
    exact MorphismProperty.of_isPullback (hπ f).flip inferInstance
  let : (D ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective π hπ
      (fun f ↦ (D.map f).injective)
  let cB := (Over.forget (Spec (.of R))).mapCocone cG
  have hcB : IsColimit cB := isColimitOfPreserves (Over.forget (Spec (.of R))) hcG
  let cD := colimit.cocone D
  let b : Cocone D := Cocone.mk cG.pt.left (π ≫ cB.ι)
  let q := colimit.desc D b
  have hcomp (j : Jᵒᵖ) : cD.ι.app j ≫ q = π.app j ≫ (cG.ι.app j).left :=
    colimit.ι_desc b j
  let (j : Jᵒᵖ) : IsProper (π.app j) := by
    rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) (e j).hom _).mpr
      (projectiveToSpec_isProper (N.obj j.unop) _)
  let : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let (j : Jᵒᵖ) : Smooth (π.app j) := by
    rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) (e j).hom _).mpr
      (projectiveToSpec_smooth (N.obj j.unop) _)
  let : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let (j : Jᵒᵖ) : GeometricallyConnected (π.app j) := by
    rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) (e j).hom _).mpr
      (projectiveToSpec_geometricallyConnected (N.obj j.unop) _)
  have hprop := bundle_properties_of_components D B π hπ cD cB
    (colimit.isColimit D) hcB q hcomp
  refine ⟨cD, q, ⟨colimit.isColimit D⟩, hcomp, ?_, hprop.1, hprop.2.1, hprop.2.2, ?_, ?_⟩
  · intro j
    exact isPullback_colimit_component D B π hπ cD cB (colimit.isColimit D) hcB q hcomp j
  · intro j
    exact (Scheme.IsLocallyDirected.openCover D).map_prop j
  · intro T f y
    let W : T.OpenCover.{u} := (Scheme.IsLocallyDirected.openCover D).pullback₁ f
    exact W.exists_eq y

end SchubertGeometry
