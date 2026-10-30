import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import Mathlib.RingTheory.FiniteType

/-! # Finite subspaces and subgroup stabilizers

A finite regular subcomodule containing generators of a vanishing ideal detects the
corresponding closed subgroup through the stabilizer of its intersection with that ideal.
-/

open TauCeti WithConv
open scoped TensorProduct

noncomputable section
namespace GroupActions

universe u v
variable {K : Type u} {H : Type v} [Field K] [CommRing H] [HopfAlgebra K H]
  [Algebra.FiniteType K H]

omit [Algebra.FiniteType K H] in
private theorem translation_mem (M : Subcomodule K H H)
    (g : WithConv (H →ₐ[K] K)) {f : H} (hf : f ∈ M) :
    HopfAlgebra.rightTranslationAlgHom g f ∈ M := by
  simpa only [HopfAlgebra.rightTranslationAlgHom_apply, ← LinearMap.lTensor_def,
    Comodule.instSelf_coact] using M.rid_lTensor_coact_mem g.ofConv.toLinearMap hf

omit [Algebra.FiniteType K H] in
private theorem translation_vanishing (S : Subgroup (WithConv (H →ₐ[K] K)))
    (g : WithConv (H →ₐ[K] K))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H)
      (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K))
    {f : H} (hf : f ∈ HopfIdeal.vanishingIdeal S) :
    HopfAlgebra.rightTranslationAlgHom g f ∈ HopfIdeal.vanishingIdeal S := by
  apply (HopfIdeal.mem_vanishingIdeal S _).mpr
  intro s
  rw [HopfAlgebra.ofConv_rightTranslationAlgHom]
  have hs := (HopfIdeal.le_vanishingIdeal_iff S (HopfIdeal.vanishingIdeal S)).mp le_rfl s.2
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
    (CommHopfAlgCat.of K H) (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) _).mp
      ((CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H)
        (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K)).mul_mem hs hg) f hf


/-- A finite regular subcomodule contains a subspace detecting the subgroup closure. -/
theorem exists_finite_subspace_stabilizer
    (S : Subgroup (WithConv (H →ₐ[K] K))) :
    ∃ (M : Subcomodule K H H) (F : Submodule K H),
      Module.Finite K M.toSubmodule ∧ F ≤ M.toSubmodule ∧
        ∀ g : WithConv (H →ₐ[K] K),
          (∀ f ∈ F, HopfAlgebra.rightTranslationAlgHom g f ∈ F) ↔
            g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H)
              (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) := by
  classical
  let I := HopfIdeal.vanishingIdeal S
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  obtain ⟨s, hs⟩ := I.toIdeal.fg_of_isNoetherianRing
  obtain ⟨M, hM, hsM⟩ := Subcomodule.exists_finite_subcomodule_of_setFinite
    (R := K) (C := H) (M := H) s.finite_toSet
  let F := M.toSubmodule ⊓ I.toIdeal.restrictScalars K
  refine ⟨M, F, hM, inf_le_left, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K H) I (CommAlgCat.of K K) g).mpr
    have hker : I.toIdeal ≤ RingHom.ker g.ofConv := by
      rw [← hs]
      apply Ideal.span_le.mpr
      intro f hf
      have hfI : f ∈ I.toIdeal := by
        rw [← hs]
        exact Ideal.subset_span hf
      have hfF : f ∈ F := ⟨hsM hf, hfI⟩
      have ht := (HopfIdeal.mem_vanishingIdeal S _).mp (hg f hfF).2 (1 : S)
      rw [HopfAlgebra.ofConv_rightTranslationAlgHom] at ht
      change g.ofConv f = 0
      simpa only [OneMemClass.coe_one, one_mul] using ht
    intro f hf
    exact hker hf
  · intro hg f hf
    exact ⟨translation_mem M g hf.1, translation_vanishing S g hg hf.2⟩

end GroupActions
