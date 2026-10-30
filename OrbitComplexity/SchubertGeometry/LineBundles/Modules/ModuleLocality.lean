import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Detecting maps and epimorphisms of module sheaves on an open cover -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory Opposite
universe u v

/-- Restriction to an open cover detects equality of module-sheaf morphisms. -/
theorem module_hom_ext_cover {X : Scheme.{u}} {I : Type v}
    {Y : I → Scheme.{u}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : (⨆ i, (j i).opensRange) = ⊤) {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (j i)).map f =
      (Scheme.Modules.restrictFunctor (j i)).map g) : f = g := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  let U : I → X.Opens := fun i => j i ''ᵁ (j i ⁻¹ᵁ V)
  have hUV (i : I) : U i ≤ V := (j i).image_preimage_le V
  have hcover : V ≤ ⨆ i, U i := by
    simp only [U, Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← iSup_inf_eq, hc, top_inf_eq]
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ U V
    (fun i => homOfLE (hUV i)) hcover
  intro i
  have hi := congrArg (fun q => q.app (j i ⁻¹ᵁ V)) (h i)
  change f.app (U i) = g.app (U i) at hi
  have hf := f.mapPresheaf.naturality (homOfLE (hUV i)).op
  have hg := g.mapPresheaf.naturality (homOfLE (hUV i)).op
  change N.presheaf.map (homOfLE (hUV i)).op (f.app V s) =
    N.presheaf.map (homOfLE (hUV i)).op (g.app V s)
  exact (ConcreteCategory.congr_hom hf s).symm.trans
    ((ConcreteCategory.congr_hom hi (M.presheaf.map (homOfLE (hUV i)).op s)).trans
      (ConcreteCategory.congr_hom hg s))

/-- Epimorphisms can be checked after restricting to an open cover. -/
theorem module_epi_cover {X : Scheme.{u}} {I : Type v}
    {Y : I → Scheme.{u}} (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hc : (⨆ i, (j i).opensRange) = ⊤) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, Epi ((Scheme.Modules.restrictFunctor (j i)).map f)) : Epi f := by
  constructor
  intro P g k hgk
  apply module_hom_ext_cover j hc
  intro i
  let F := Scheme.Modules.restrictFunctor (j i)
  let : Epi (F.map f) := h i
  apply (cancel_epi (F.map f)).mp
  exact (F.map_comp f g).symm.trans
    ((congrArg F.map hgk).trans (F.map_comp f k))

end SchubertGeometry.ProjectiveLine
