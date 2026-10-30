import OrbitComplexity.SchubertGeometry.Normality.Bundles.ModelBundleData
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveBundle
import OrbitComplexity.SchubertGeometry.Normality.Bundles.BorelModelProjective

/-! # The same retained Borel coefficients construct a projective bundle -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FrobeniusSplitting
open ReductiveGroups GroupActions
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

private theorem bundle_of_parameters {I R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (H : modelProjectiveSpec N F e sel c a) : modelBundleSpec N F e sel c a cG := by
  obtain ⟨c₀, a₀, hc₀, ha₀, hco₀, hn₀, H⟩ := H
  obtain ⟨D, eP, π, hproj, hmap, hcart⟩ := H
  refine ⟨c₀, a₀, hc₀, ha₀, hco₀, hn₀, D, eP, π, hproj, hmap, hcart, ?_⟩
  exact exists_projective_bundle N D π hcart (fun s ↦ eP s.unop)
    (fun s ↦ hproj s.unop) cG hcG

end SchubertGeometry
