import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open Covers

Open immersions can be checked on restrictions covering the source.
-/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

/-- Open immersions on restrictions covering the source give an open immersion. -/
theorem isOpenImmersion_of_restrict_cover {X Y : Scheme} {I : Type*}
    (f : X ⟶ Y) (U : I → Y.Opens) (hcover : (⨆ i, f ⁻¹ᵁ U i) = ⊤)
    (hlocal : ∀ i, IsOpenImmersion (f ∣_ U i)) : IsOpenImmersion f := by
  have (i : I) : IsOpenImmersion (f ∣_ U i) := hlocal i
  have hf : Function.Injective f := by
    intro x y h
    have hx : x ∈ ⨆ i, f ⁻¹ᵁ U i := hcover.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hyi : y ∈ f ⁻¹ᵁ U i := by
      change f y ∈ U i
      rw [← h]
      exact hxi
    have he : (f ∣_ U i) ⟨x, hxi⟩ = (f ∣_ U i) ⟨y, hyi⟩ := by
      apply Subtype.ext
      exact (morphismRestrict_base_coe f (U i) ⟨x, hxi⟩).trans
        (h.trans (morphismRestrict_base_coe f (U i) ⟨y, hyi⟩).symm)
    exact congrArg Subtype.val ((f ∣_ U i).isOpenEmbedding.injective he)
  let 𝒰 := X.openCoverOfIsOpenCover (fun i ↦ f ⁻¹ᵁ U i) hcover
  apply IsOpenImmersion.of_openCover_source f 𝒰 hf
  intro i
  change IsOpenImmersion ((f ⁻¹ᵁ U i).ι ≫ f)
  rw [← morphismRestrict_ι]
  have : IsOpenImmersion (f ∣_ U i) := hlocal i
  infer_instance

end FrobeniusSplitting
