import OrbitComplexity.FrobeniusSplitting.Splittings.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Batteries.Tactic.Lint

/-! # Splittings on a closed subscheme from an ambient cover

Local splittings commuting with the same ambient splitting agree on overlaps.
Surjectivity of restriction to an affine closed subscheme proves the local
equality, and the sheaf condition extends it to arbitrary open subsets.
-/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u
namespace FrobeniusSplitting.SchemeSplitting

private theorem affine_preimage_neighbourhood {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsClosedImmersion j] (W : Y.Opens) (A B : X.Opens)
    (ha : W ≤ j ⁻¹ᵁ A) (hb : W ≤ j ⁻¹ᵁ B) (x : Y) (hx : x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ j x ∈ V ∧ V ≤ A ∧ V ≤ B ∧ j ⁻¹ᵁ V ≤ W := by
  obtain ⟨O, hO, hpre⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let T : X.Opens := ⟨O, hO⟩ ⊓ (A ⊓ B)
  have hxO : j x ∈ O := by
    change x ∈ j ⁻¹' O
    rw [hpre]
    exact hx
  have hxT : j x ∈ T := ⟨hxO, ha hx, hb hx⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxT T.isOpen
  refine ⟨V, hV, hxV, (fun _ h => (hVT h).2.1), (fun _ h => (hVT h).2.2), ?_⟩
  intro y hy
  change y ∈ (W : Set Y)
  rw [← hpre]
  exact (hVT hy).1

private theorem closedCover_compatible {X Y : Scheme.{u}} {p : ℕ}
    (j : Y ⟶ X) [IsClosedImmersion j] (ambient : SchemeSplitting X p)
    {I : Type u} (U : I → X.Opens)
    (localSplitting : ∀ i, SchemeSplitting (j ⁻¹ᵁ U i).toScheme p)
    (hlocal : ∀ i (V : X.Opens) (hV : V ≤ U i) (a : Γ(X, V)),
      (localSplitting i).onSubopen (j ⁻¹ᵁ V) (fun _ hx => hV hx) (j.app V a) =
        j.app V (ambient.onOpen V a))
    (i k : I) (W : Y.Opens) (hi : W ≤ j ⁻¹ᵁ U i) (hk : W ≤ j ⁻¹ᵁ U k) :
    (localSplitting i).onSubopen W hi = (localSplitting k).onSubopen W hk := by
  apply RingSplitting.ext
  intro a
  apply Y.IsSheaf.section_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVi, hVk, hVW⟩ :=
    affine_preimage_neighbourhood j W (U i) (U k) hi hk x hx
  refine ⟨j ⁻¹ᵁ V, hVW, hxV, ?_⟩
  obtain ⟨b, hb⟩ := j.app_surjective V hV (Y.presheaf.map (homOfLE hVW).op a)
  have hsmall :
      (localSplitting i).onSubopen (j ⁻¹ᵁ V) (hVW.trans hi)
        (Y.presheaf.map (homOfLE hVW).op a) =
      (localSplitting k).onSubopen (j ⁻¹ᵁ V) (hVW.trans hk)
        (Y.presheaf.map (homOfLE hVW).op a) := by
    calc
      _ = (localSplitting i).onSubopen (j ⁻¹ᵁ V) (hVW.trans hi) (j.app V b) :=
        congrArg ((localSplitting i).onSubopen (j ⁻¹ᵁ V) (hVW.trans hi)) hb.symm
      _ = j.app V (ambient.onOpen V b) := hlocal i V hVi b
      _ = (localSplitting k).onSubopen (j ⁻¹ᵁ V) (hVW.trans hk) (j.app V b) :=
        (hlocal k V hVk b).symm
      _ = _ := congrArg ((localSplitting k).onSubopen (j ⁻¹ᵁ V) (hVW.trans hk)) hb
  exact ((localSplitting i).onSubopen_restrict hi hVW a).symm.trans
    (hsmall.trans ((localSplitting k).onSubopen_restrict hk hVW a))

/-- Splittings on the inverse images of an ambient open cover glue when their
closed projections commute with the same ambient splitting. -/
def glueClosedCover {X Y : Scheme.{u}} {p : ℕ}
    (j : Y ⟶ X) [IsClosedImmersion j] (ambient : SchemeSplitting X p)
    {I : Type u} (U : I → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (localSplitting : ∀ i, SchemeSplitting (j ⁻¹ᵁ U i).toScheme p)
    (hlocal : ∀ i (V : X.Opens) (hV : V ≤ U i) (a : Γ(X, V)),
      (localSplitting i).onSubopen (j ⁻¹ᵁ V) (fun _ hx => hV hx) (j.app V a) =
        j.app V (ambient.onOpen V a)) : SchemeSplitting Y p :=
  glue (fun i => j ⁻¹ᵁ U i) localSplitting
    (closedCover_compatible j ambient U localSplitting hlocal) (by
      apply top_unique
      intro y _
      have hy : j y ∈ ⨆ i, U i := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)

end FrobeniusSplitting.SchemeSplitting
