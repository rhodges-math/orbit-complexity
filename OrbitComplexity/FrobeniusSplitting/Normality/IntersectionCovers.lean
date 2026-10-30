import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteCover
import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# Open covers by finite intersections
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

variable {X : Scheme.{u}} {I : Type u}

private theorem intersection_iSup (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤) :
    (⨆ s, (intersectionOpens U).obj s) = ⊤ := by
  classical
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ ⨆ i, U i := hcover.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨.op ⟨{i}, Finset.singleton_nonempty i⟩, ?_⟩
  simpa only [intersectionOpens, Finset.mem_singleton, iInf_iInf_eq_left] using hi

/-- The nonempty finite intersections of an open cover form an open cover. -/
noncomputable abbrev intersectionCover (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤) :
    X.OpenCover := X.openCoverOfIsOpenCover ((intersectionOpens U).obj)
      (intersection_iSup U hcover)

/-- The intersection cover carries the reverse-inclusion category of its finite index sets. -/
@[instance_reducible]
noncomputable def intersectionCoverCategory
    (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤) :
    Category.{u} (intersectionCover U hcover).I₀ := by
  change Category.{u} {s : Finset I // s.Nonempty}ᵒᵖ
  infer_instance

attribute [local instance] intersectionCoverCategory

/-- The finite-intersection cover is locally directed by union of its index sets. -/
@[instance_reducible]
noncomputable def intersectionCoverDirected
    (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤) :
    (intersectionCover U hcover).LocallyDirected where
  trans {s t} f := ((intersectionOpens U) ⋙ X.restrictFunctor ⋙ Over.forget X).map f
  trans_id s := ((intersectionOpens U) ⋙ X.restrictFunctor ⋙ Over.forget X).map_id s
  trans_comp f g := ((intersectionOpens U) ⋙ X.restrictFunctor ⋙ Over.forget X).map_comp f g
  w {s t} f := by
    change X.homOfLE (leOfHom ((intersectionOpens U).map f)) ≫
      ((intersectionOpens U).obj t).ι = ((intersectionOpens U).obj s).ι
    exact Scheme.homOfLE_ι X _
  directed {s t} x := by
    classical
    change {s : Finset I // s.Nonempty}ᵒᵖ at s t
    let v : {s : Finset I // s.Nonempty}ᵒᵖ :=
      .op ⟨s.unop.val ∪ t.unop.val, s.unop.property.mono Finset.subset_union_left⟩
    let fs : v ⟶ s := (homOfLE (show s.unop ≤ v.unop from Finset.subset_union_left)).op
    let ft : v ⟶ t := (homOfLE (show t.unop ≤ v.unop from Finset.subset_union_right)).op
    let p := pullback.fst ((intersectionCover U hcover).f s)
      ((intersectionCover U hcover).f t)
    let q := pullback.snd ((intersectionCover U hcover).f s)
      ((intersectionCover U hcover).f t)
    have : IsOpenImmersion ((intersectionCover U hcover).f t) :=
      (intersectionCover U hcover).map_prop t
    have : IsOpenImmersion p := by
      change IsOpenImmersion (pullback.fst ((intersectionCover U hcover).f s)
        ((intersectionCover U hcover).f t))
      infer_instance
    have hpq : ((p x).val : X) = (q x).val := by
      exact congr($(pullback.condition (f := (intersectionCover U hcover).f s)
        (g := (intersectionCover U hcover).f t)) x)
    have hz : (p x).val ∈ (intersectionOpens U).obj v := by
      have hv : (intersectionOpens U).obj v =
          (intersectionOpens U).obj s ⊓ (intersectionOpens U).obj t :=
        Finset.iInf_union
      rw [hv]
      exact ⟨(p x).property, hpq.symm ▸ (q x).property⟩
    refine ⟨v, fs, ft, ⟨(p x).val, hz⟩, ?_⟩
    apply p.isOpenEmbedding.injective
    change (pullback.lift
      (((intersectionOpens U) ⋙ X.restrictFunctor ⋙ Over.forget X).map fs)
      (((intersectionOpens U) ⋙ X.restrictFunctor ⋙ Over.forget X).map ft) _ ≫
        pullback.fst ((intersectionCover U hcover).f s)
          ((intersectionCover U hcover).f t)) ⟨(p x).val, hz⟩ = p x
    erw [pullback.lift_fst]
    apply Subtype.ext
    exact Scheme.homOfLE_apply (leOfHom ((intersectionOpens U).map fs)) ⟨(p x).val, hz⟩
  property_trans f := by
    change IsOpenImmersion (X.homOfLE (leOfHom ((intersectionOpens U).map f)))
    infer_instance

/-- A scheme is the colimit of the restriction diagram of finite intersections of its open cover. -/
noncomputable def intersectionCoverIsColimit
    (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤) :
    letI := intersectionCoverDirected U hcover
    IsColimit (Scheme.Cover.coconeOfLocallyDirected (intersectionCover U hcover)) := by
  letI := intersectionCoverDirected U hcover
  exact Scheme.OpenCover.isColimitCoconeOfLocallyDirected _

end FrobeniusSplitting
