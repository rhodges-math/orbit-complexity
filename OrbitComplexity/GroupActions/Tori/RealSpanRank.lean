import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.EuclideanDomain.Int

/-! # Real dimensions of character spans

An integer-coordinate family has the same span rank over the integers and the reals. Integral
lattice bases remain independent after applying the coordinate map into the reals.

## Main results

* `GroupActions.finrank_realSpan`: real span dimension equals integral lattice rank.
-/

open Module Submodule

namespace GroupActions

universe u v

noncomputable section

/-- The real span of integer vectors has the integral rank of their integral span. -/
theorem finrank_realSpan {ι : Type u} {κ : Type v} [Finite κ] (w : ι → κ → ℤ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i k ↦ (w i k : ℝ)))) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range w)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let N := Submodule.span ℤ (Set.range w)
  obtain ⟨n, b⟩ := N.basisOfPid (Pi.basisFun ℤ κ)
  let v : Fin n → κ → ℤ := fun i ↦ (b i).val
  have hv : LinearIndependent ℤ v :=
    b.linearIndependent.map' N.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hvr : LinearIndependent ℝ (fun i k ↦ (v i k : ℝ)) := by
    exact linearIndependent_algebraMap_comp_iff.mpr hv
  have hspan : Submodule.span ℤ (Set.range v) = N := by
    have h := congrArg (Submodule.map N.subtype) b.span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, Submodule.range_subtype, Submodule.subtype_apply, v] using h
  let c : (κ → ℤ) →ₗ[ℤ] (κ → ℝ) := Pi.algebraMap κ ℤ ℝ
  have hm : Submodule.span ℤ (Set.range (fun i k ↦ (w i k : ℝ))) =
      Submodule.span ℤ (Set.range (fun i k ↦ (v i k : ℝ))) := by
    have h := congrArg (Submodule.map c) hspan.symm
    simpa [Submodule.map_span, ← Set.range_comp, Function.comp_def, c, N,
      Pi.algebraMap] using h
  have hr : Submodule.span ℝ (Set.range (fun i k ↦ (w i k : ℝ))) =
      Submodule.span ℝ (Set.range (fun i k ↦ (v i k : ℝ))) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ, hm, Submodule.span_span_of_tower]
  rw [hr, finrank_span_eq_card hvr, ← Module.finrank_eq_card_basis b]

/-- The real span of integer coefficient vectors has their integral lattice rank. -/
theorem finrank_realSpan_finsupp {ι : Type u} {κ : Type v} [Finite κ] (w : ι → κ →₀ ℤ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i k ↦ (w i k : ℝ)))) =
      Module.finrank ℤ (Submodule.span ℤ (Set.range w)) := by
  let e := Finsupp.linearEquivFunOnFinite ℤ ℤ κ
  have h := finrank_realSpan (fun i ↦ e (w i))
  have he := e.finrank_map_eq (Submodule.span ℤ (Set.range w))
  rw [Submodule.map_span, ← Set.range_comp] at he
  exact h.trans he


end

end GroupActions
