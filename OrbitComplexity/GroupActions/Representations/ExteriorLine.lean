import TauCeti.LinearAlgebra.ExteriorPower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Stabilizers of top exterior lines

The top exterior product of a basis of a finite-dimensional subspace is nonzero. Its
wedge annihilator recovers the subspace, and its line has the same linear stabilizer.
-/

noncomputable section
namespace GroupActions
open CliffordAlgebra

universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

private def topVector (F : Submodule K V) {d : ℕ} (b : Module.Basis (Fin d) K F) :
    ⋀[K]^d V :=
  exteriorPower.map d F.subtype (exteriorPower.ιMulti K d b)

private theorem topVector_ne_zero (F : Submodule K V) {d : ℕ}
    (b : Module.Basis (Fin d) K F) : topVector F b ≠ 0 := by
  intro hz
  have ht : exteriorPower.ιMulti K d b = 0 :=
    (exteriorPower.map_injective_field F.subtype_injective)
      (hz.trans (map_zero _).symm)
  have h := congrArg (exteriorPower.topEquiv b) ht
  exact one_ne_zero (by
    simpa only [exteriorPower.topEquiv_apply_ιMulti, Module.Basis.det_self, map_zero] using h)

private theorem contract_top {d : ℕ} (φ : Module.Dual K V) (a : Fin d → V)
    (ha : ∀ i, φ (a i) = 0) :
    contractLeft (Q := (0 : QuadraticForm K V)) φ (ExteriorAlgebra.ιMulti K d a) = 0 := by
  induction d with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply, contractLeft_one]
  | succ d ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ha 0, zero_smul,
        ih (Matrix.vecTail a) (fun i => ha i.succ), mul_zero, sub_zero]

private theorem wedge_top_iff (F : Submodule K V) [Module.Finite K F] {d : ℕ}
    (b : Module.Basis (Fin d) K F) (x : V) :
    ExteriorAlgebra.ι K x * (topVector F b).val = 0 ↔ x ∈ F := by
  constructor
  · intro hx
    by_contra hxF
    obtain ⟨φ, hφx, hFφ⟩ := Submodule.exists_le_ker_of_notMem hxF
    have hφ : contractLeft (Q := (0 : QuadraticForm K V)) φ
        (topVector F b).val = 0 := by
      rw [topVector, exteriorPower.coe_map, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.map_apply_ιMulti]
      exact contract_top φ _ fun i => hFφ (b i).2
    have h := congrArg (contractLeft (Q := (0 : QuadraticForm K V)) φ) hx
    rw [contractLeft_ι_mul, hφ, mul_zero, sub_zero, map_zero] at h
    have hw : (topVector F b).val ≠ 0 := by
      intro hzero
      exact topVector_ne_zero F b (Subtype.ext hzero)
    exact (smul_eq_zero.mp h).elim hφx hw
  · intro hx
    have hd : Module.finrank K F < d + 1 := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
      omega
    have hz := exteriorPower.eq_zero_of_finrank_lt (d + 1) hd
      (exteriorPower.ιMulti K (d + 1) (Fin.cons (⟨x, hx⟩ : F) b))
    have h := congrArg
      (fun z : ⋀[K]^(d + 1) F => ExteriorAlgebra.map F.subtype z.val) hz
    simpa [topVector, exteriorPower.coe_map, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_succ_apply,
      Matrix.vecTail, Function.comp_def] using h


private theorem map_top_of_stable (F : Submodule K V) [Module.Finite K F]
    (b : Module.Basis (Fin (Module.finrank K F)) K F) (e : V ≃ₗ[K] V)
    (hF : F.map e.toLinearMap = F) :
    exteriorPower.map (Module.finrank K F) e.toLinearMap (topVector F b) =
      LinearMap.det (e.ofSubmodules F F hF).toLinearMap • topVector F b := by
  let eF := e.ofSubmodules F F hF
  have hc : e.toLinearMap.comp F.subtype = F.subtype.comp eF.toLinearMap := rfl
  dsimp only [topVector]
  calc
    exteriorPower.map _ e.toLinearMap
        (exteriorPower.map _ F.subtype (exteriorPower.ιMulti K _ b)) =
      exteriorPower.map _ (e.toLinearMap.comp F.subtype)
        (exteriorPower.ιMulti K _ b) :=
      (LinearMap.congr_fun (exteriorPower.map_comp F.subtype e.toLinearMap) _).symm
    _ = exteriorPower.map _ (F.subtype.comp eF.toLinearMap)
        (exteriorPower.ιMulti K _ b) := by rw [hc]
    _ = exteriorPower.map _ F.subtype
        (exteriorPower.map _ eF.toLinearMap (exteriorPower.ιMulti K _ b)) :=
      LinearMap.congr_fun (exteriorPower.map_comp eF.toLinearMap F.subtype) _
    _ = _ := by
      rw [exteriorPower.map_finrank_eq_det_smul]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]
      rfl

/-- A finite-dimensional subspace has a top exterior vector with its determinant action and
the same stabilizer. -/
theorem exists_exterior_line_stabilizer (F : Submodule K V) [Module.Finite K F] :
    ∃ w : ⋀[K]^(Module.finrank K F) V, w ≠ 0 ∧
      (∀ (e : V ≃ₗ[K] V) (hF : F.map e.toLinearMap = F),
        exteriorPower.map (Module.finrank K F) e.toLinearMap w =
          LinearMap.det (e.ofSubmodules F F hF).toLinearMap • w) ∧
      ∀ e : V ≃ₗ[K] V,
        (Submodule.span K {w}).map
            (exteriorPower.map (Module.finrank K F) e.toLinearMap) =
          Submodule.span K {w} ↔ F.map e.toLinearMap = F := by
  let b := Module.finBasis K F
  let w := topVector F b
  have hw : w ≠ 0 := topVector_ne_zero F b
  refine ⟨w, hw, (fun e hF => map_top_of_stable F b e hF), fun e => ⟨?_, ?_⟩⟩
  · intro he
    have hmem : exteriorPower.map _ e.toLinearMap w ∈ Submodule.span K {w} := by
      rw [← he]
      exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := by
      intro hz
      have hew : exteriorPower.map _ e.toLinearMap w = 0 := by
        rw [← hc, hz, zero_smul]
      exact hw ((exteriorPower.map_injective_field e.injective)
        (hew.trans (map_zero _).symm))
    apply Submodule.eq_of_le_of_finrank_eq ?_ (e.finrank_map_eq F)
    rintro y ⟨x, hx, rfl⟩
    apply (wedge_top_iff F b (e x)).mp
    have hzero := congrArg (ExteriorAlgebra.map e.toLinearMap)
      ((wedge_top_iff F b x).mpr hx)
    rw [map_mul, ExteriorAlgebra.map_apply_ι, map_zero] at hzero
    have htop : ExteriorAlgebra.map e.toLinearMap w.val = c • w.val := by
      simpa only [exteriorPower.coe_map, Submodule.coe_smul] using
        (congrArg Subtype.val hc).symm
    rw [htop, mul_smul_comm] at hzero
    exact (smul_eq_zero.mp hzero).resolve_left hc0
  · intro hF
    rw [Submodule.map_span, Set.image_singleton, map_top_of_stable F b e hF]
    exact Submodule.span_singleton_smul_eq (e.ofSubmodules F F hF).isUnit_det' _

end GroupActions
