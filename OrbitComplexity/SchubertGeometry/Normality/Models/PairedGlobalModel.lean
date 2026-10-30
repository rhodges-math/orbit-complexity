import OrbitComplexity.FrobeniusSplitting.Normality.Images.IntersectionModel
import OrbitComplexity.SchubertGeometry.Normality.Models.PairedFamily

/-! # Smooth arithmetic models of the paired source -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions FrobeniusSplitting
open scoped TensorProduct
namespace SchubertGeometry
noncomputable section
universe u v w

/-- A finite affine cover of the paired source constructs a smooth arithmetic
model and its Cartesian comparison with the paired source. -/
theorem pairedBSDH_global_source_model
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    {I : Type u} [Finite I]
    [IsAffineHom (pullback.diagonal (terminal.from (pairedBSDHSource G a b).left))]
    (U : I → (pairedBSDHSource G a b).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (P : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ s, Algebra.FinitePresentation S (P.obj s)] [∀ s, Module.Flat S (P.obj s)]
    (e : ∀ s, K ⊗[S] P.obj s ≃ₐ[K]
      (intersectionCoordinates (pairedBSDHSource G a b).hom (intersectionOpens U)).obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
      ((intersectionCoordinates (pairedBSDHSource G a b).hom (intersectionOpens U)).map f).hom.comp
        (e s).toAlgHom) :
    ∃ (R : Subalgebra ℤ K) (_ : S ≤ R) (C : Over (Spec (.of R)))
      (q : (pairedBSDHSource G a b).left ⟶ C.left),
      R.FG ∧ CompactSpace C.left ∧ Smooth C.hom ∧ LocallyOfFinitePresentation C.hom ∧
      IsPullback q (pairedBSDHSource G a b).hom C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  classical
  let X := pairedBSDHSource G a b
  let C := {s : Finset I // s.Nonempty}
  let F := intersectionCoordinates X.hom (intersectionOpens U)
  let E := intersectionOpens U ⋙ X.left.restrictFunctor ⋙ Over.map X.hom
  let (s : Cᵒᵖ) : IsAffine (E.obj s).left := intersectionOpens_affine U hU s
  let j (s : C) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s)))) ⟶ X :=
    (intersectionCoordinateCocone X.hom U hU).ι.app (Opposite.op s)
  let (s : C) : IsOpenImmersion (j s).left := by
    let iso := (Over.forget (Spec (.of K))).mapIso
      ((coordinateDiagramIso (.of K) E).app (Opposite.op s))
    let V := (intersectionOpens U).obj (Opposite.op s)
    let inc : V.toScheme ⟶ X.left := V.ι
    have hIso : IsOpenImmersion iso.inv := inferInstance
    have hInc : IsOpenImmersion inc := IsOpenImmersion.ofRestrict X.left V.isOpenEmbedding
    change IsOpenImmersion (iso.inv ≫ inc)
    exact @IsOpenImmersion.comp _ _ _ iso.inv inc hIso hInc
  obtain ⟨T, hST, _H0, _hH0, _hAlgH0, _eH0, _eps0, hT, _hsmH0, hsmP,
    _hsmprod, _hsection, heT, _heps0, _hproj, _hretract, _hnatural, _hfibres⟩ :=
    pairedBSDH_family_model G a b S hS P F j e he
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let P_T := fixedFibreDiagram (R := T) (M := T) P
  let eT (s : C) := (Algebra.TensorProduct.cancelBaseChange S T K K (P.obj s)).trans (e s)
  let (s : C) : Algebra.Smooth T (P_T.obj s) := hsmP s
  have hopen : ∀ s t (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) := by
    intro s t f
    exact coordinateMaps_open (.of K) E (fun s t g => by
      change IsOpenImmersion (X.left.homOfLE (leOfHom ((intersectionOpens U).map g)))
      infer_instance) f.op
  obtain ⟨R, hTR, _heR', cN, q, hR, _hcN, hcart, _hleg, hcompact, hlfp,
      hsmooth, _hopenN, _hcovN, _hbc, _hnormal⟩ :=
    @FrobeniusSplitting.exists_intersection_model.{u} X.left I K inferInstance
      (inferInstanceAs (CommRing K)) inferInstance X.hom U hU hcover T hT P_T
      (fun s => inferInstance) (fun s => inferInstance) eT heT hopen
  exact ⟨R, hST.trans hTR, cN.pt, q, hR, hcompact, hsmooth, hlfp, hcart⟩

end
end SchubertGeometry
