import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.OpenDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionSquares
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateColimits
import OrbitComplexity.FrobeniusSplitting.Normality.AffineModelDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.GluedBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.GluedFiniteness

/-!
# Arithmetic models of quasi-compact schemes
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- A quasi-compact scheme with affine diagonal descends to a finitely generated
coefficient ring. -/
theorem exists_arithmetic_scheme {X : Scheme.{u}} {K : Type u} [CommRing K]
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    ∃ (R : Subalgebra ℤ K) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of R)) (q : X ⟶ X₀),
      R.FG ∧ CompactSpace X₀ ∧ LocallyOfFinitePresentation f₀ ∧
      IsPullback q f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  classical
  obtain ⟨I, finiteI, U, hU, hcover⟩ := exists_finite_affine_opens X
  have : Finite I := finiteI
  let C := {s : Finset I // s.Nonempty}
  have : Finite {s : Finset I // s.Nonempty}ᵒᵖ :=
    Finite.of_injective Opposite.unop Opposite.unop_injective
  let D := intersectionCoordinates f (intersectionOpens U)
  let E := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have (s : Cᵒᵖ) : IsAffine (E.obj s).left := intersectionOpens_affine U hU s
  have (s : C) : Algebra.FinitePresentation K (D.obj s) := by
    have : LocallyOfFinitePresentation (E.obj (.op s)).hom := by
      change LocallyOfFinitePresentation (((intersectionOpens U).obj (.op s)).ι ≫ f)
      infer_instance
    change ((E.obj (.op s)).hom.appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).FinitePresentation
    exact (E.obj (.op s)).hom.finitePresentation_appTop.comp
      (RingHom.FinitePresentation.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv))
  have hopen : ∀ i j (g : i ⟶ j), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (D.map g).hom.toRingHom)) := by
    intro i j g
    exact coordinateMaps_open (.of K) E (fun i j g ↦ by
      change IsOpenImmersion (X.homOfLE (leOfHom ((intersectionOpens U).map g)))
      infer_instance) g.op
  obtain ⟨R, D₀, e, hfg, hfp, _, hnatural, hopen₀, hpush⟩ :=
    exists_open_arithmetic_diagram D hopen ∅ (by simp)
  let (i : C) : Algebra.FinitePresentation R (D₀.obj i) := hfp i
  let F := D.op ⋙ algSpec (.of K)
  let G := D₀.op ⋙ algSpec (.of R)
  have {i j : Cᵒᵖ} (g : i ⟶ j) : IsOpenImmersion (G.map g).left :=
    hopen₀ j.unop i.unop g.unop
  have : ((G ⋙ Over.forget (Spec (.of R))) ⋙ Scheme.forget).IsLocallyDirected := by
    apply locallyDirected_of_pullbacks
    intro i j k gi gj
    obtain ⟨l, hi, hj, hgeneric⟩ := intersectionCoordinates_refine f U hU i j k gi gj
    refine ⟨l, hi, hj, ?_⟩
    change IsPullback
      (Spec.map (CommRingCat.ofHom (D₀.map hi.unop).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D₀.map hj.unop).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D₀.map gi.unop).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D₀.map gj.unop).hom.toRingHom))
    exact (isPushout_iff_spec_pullback _ _ _ _).mp
      (hpush k.unop i.unop j.unop l.unop gi.unop gj.unop hi.unop hj.unop hgeneric)
  obtain ⟨cF, cG, q, ⟨hcF⟩, ⟨hcG⟩, hcart⟩ := exists_glued_baseChange F G
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (affineModelNatTrans D₀ D e hnatural) (affineModel_equifibered D₀ D e hnatural)
    (fun i ↦ by
      let : Algebra R (D.obj i.unop) :=
        ((algebraMap K (D.obj i.unop)).comp (algebraMap R K)).toAlgebra
      have htower : IsScalarTower R K (D.obj i.unop) :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      exact (@isPullback_affineModel R K (D₀.obj i.unop) (D.obj i.unop)
        _ _ _ _ _ _ _ _ htower (e i.unop)).flip)
  have (i : Cᵒᵖ) : IsAffine (G.obj i).left := by
    change IsAffine (Spec (.of (D₀.obj i.unop)))
    infer_instance
  have (i : Cᵒᵖ) : LocallyOfFinitePresentation (G.obj i).hom := by
    change LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (D₀.obj i.unop))))
    apply (LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R (D₀.obj i.unop)))).mpr
    change (algebraMap R (D₀.obj i.unop)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact hfp i.unop
  obtain ⟨hcompact, hfp₀⟩ := finite_affine_colimit_properties G cG hcG
  obtain ⟨cX, heq, ⟨hcX⟩⟩ := exists_coordinate_colimit f U hU hcover
  let isoX := (eqToIso heq).symm ≪≫ hcX.coconePointUniqueUpToIso hcF
  let isoS := (Over.forget (Spec (.of K))).mapIso isoX
  have hcartX : IsPullback (isoS.hom ≫ q) f cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    apply hcart.of_iso' isoS (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · change isoX.hom.left ≫ cF.pt.hom = f ≫ 𝟙 (Spec (.of K))
      rw [Category.comp_id]
      exact Over.w isoX.hom
    · simp
    · simp
  exact ⟨R, cG.pt.left, cG.pt.hom, isoS.hom ≫ q, hfg, hcompact, hfp₀, hcartX⟩

end FrobeniusSplitting
