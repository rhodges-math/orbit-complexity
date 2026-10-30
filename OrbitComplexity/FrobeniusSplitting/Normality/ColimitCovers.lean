import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# Colimit covers of locally directed scheme diagrams
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- Pullback refinements of cospans make a scheme diagram locally directed on points. -/
theorem locallyDirected_of_pullbacks {J : Type v} [Category.{w} J]
    (F : J ⥤ Scheme.{u})
    (h : ∀ (i j k : J) (fi : i ⟶ k) (fj : j ⟶ k),
      ∃ (l : J) (gi : l ⟶ i) (gj : l ⟶ j),
        IsPullback (F.map gi) (F.map gj) (F.map fi) (F.map fj)) :
    (F ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj heq := by
    obtain ⟨l, gi, gj, hcart⟩ := h i j k fi fj
    obtain ⟨z, hzi, hzj⟩ := Scheme.exists_preimage_of_isPullback hcart xi xj heq
    exact ⟨l, gi, gj, z, hzi, hzj⟩

/-- The component cover of a locally directed diagram has its original index category. -/
@[instance_reducible]
noncomputable def colimitCoverCategory {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (F : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F ⋙ Scheme.forget).IsLocallyDirected] :
    Category.{w} (Scheme.IsLocallyDirected.openCover F).I₀ := by
  change Category.{w} J
  infer_instance

/-- The component cover of a locally directed open diagram retains its transition maps. -/
@[instance_reducible]
noncomputable def colimitCoverDirected {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (F : J ⥤ Scheme.{u})
    [hopen : ∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F ⋙ Scheme.forget).IsLocallyDirected] :
    letI := colimitCoverCategory F
    (Scheme.IsLocallyDirected.openCover F).LocallyDirected := by
  letI := colimitCoverCategory F
  refine
    { trans := F.map
      trans_id := F.map_id
      trans_comp := F.map_comp
      w := colimit.w F
      directed := ?_
      property_trans := fun f ↦ hopen f }
  intro i j x
  change J at i j
  let 𝒰 := Scheme.IsLocallyDirected.openCover F
  have h : colimit.ι F i ((pullback.fst (𝒰.f i) (𝒰.f j)) x) =
      colimit.ι F j ((pullback.snd (𝒰.f i) (𝒰.f j)) x) := by
    exact congr($(pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) x)
  obtain ⟨k, fi, fj, z, hz, _⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
  refine ⟨k, fi, fj, z, ?_⟩
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  apply (pullback.fst (𝒰.f i) (𝒰.f j)).isOpenEmbedding.injective
  change (pullback.lift (F.map fi) (F.map fj) _ ≫ pullback.fst (𝒰.f i) (𝒰.f j)) z = _
  erw [pullback.lift_fst]
  exact hz


end FrobeniusSplitting
