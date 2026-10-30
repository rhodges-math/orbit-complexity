import OrbitComplexity.GroupActions.Representations.ChevalleySubspace
import OrbitComplexity.GroupActions.Representations.ExteriorLine
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.RepresentationTheory.ExteriorPower

/-! # Exterior lines of regular comodules

The induced action on a finite regular subcomodule has an exterior line whose stabilizer
is the subgroup defined by the vanishing ideal.
-/

noncomputable section
namespace GroupActions
open TauCeti WithConv
open scoped TensorProduct

universe u v
variable {K : Type u} {H : Type v} [Field K] [CommRing H] [HopfAlgebra K H]

private def baseActionEquiv (M : Subcomodule K H H) (g : WithConv (H →ₐ[K] K)) :
    M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap
    (Comodule.basePointsRepresentation (H := H) M g)
    (Comodule.basePointsRepresentation (H := H) M g⁻¹)
    (by
      change Comodule.basePointsRepresentation (H := H) M g *
        Comodule.basePointsRepresentation (H := H) M g⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one])
    (by
      change Comodule.basePointsRepresentation (H := H) M g⁻¹ *
        Comodule.basePointsRepresentation (H := H) M g = 1
      rw [← map_mul, inv_mul_cancel, map_one])

private theorem base_action_coe (M : Subcomodule K H H) (g : WithConv (H →ₐ[K] K))
    (m : M) :
    ((Comodule.basePointsRepresentation (H := H) M g m : M) : H) =
      HopfAlgebra.rightTranslationAlgHom g m := by
  have hn (z : M ⊗[K] H) :
      (TensorProduct.rid K M (LinearMap.lTensor M g.ofConv.toLinearMap z) : H) =
        TensorProduct.rid K H (LinearMap.lTensor H g.ofConv.toLinearMap
          ((SMulMemClass.subtype M).rTensor H z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul m h => simp
    | add z w hz hw => simpa only [map_add, AddMemClass.coe_add] using congrArg₂ (· + ·) hz hw
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, one_smul,
    TensorProduct.lid_comm]
  change (TensorProduct.rid K M
    (LinearMap.lTensor M g.ofConv.toLinearMap (M.inducedCoact m)) : H) = _
  rw [hn, M.subtype_rTensor_inducedCoact, HopfAlgebra.rightTranslationAlgHom_apply]
  rfl


/-- A finite regular comodule yields an exterior line with the prescribed closed stabilizer. -/
theorem exists_comodule_line_stabilizer [Algebra.FiniteType K H]
    (S : Subgroup (WithConv (H →ₐ[K] K))) :
    ∃ M : Subcomodule K H H,
      letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
      Module.Finite K M ∧
        ∃ (d : ℕ) (w : ⋀[K]^d M), w ≠ 0 ∧
          ∀ g : WithConv (H →ₐ[K] K),
            (Submodule.span K {w}).map
                (Representation.exteriorPower
                  (Comodule.basePointsRepresentation (R := K) (H := H) M) d g) =
              Submodule.span K {w} ↔
                g ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K H)
                  (HopfIdeal.vanishingIdeal S) (CommAlgCat.of K K) := by
  obtain ⟨M, F, hM, hFM, hS⟩ := GroupActions.exists_finite_subspace_stabilizer S
  refine ⟨M, ?_⟩
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  let : Module.Finite K M := hM
  let N : Submodule K M := F.comap (SMulMemClass.subtype M)
  obtain ⟨w, hw, _hdet, hew⟩ := GroupActions.exists_exterior_line_stabilizer N
  refine ⟨hM, Module.finrank K N, w, hw, fun g => ?_⟩
  change (Submodule.span K {w}).map
      (exteriorPower.map _ (baseActionEquiv M g).toLinearMap) =
    Submodule.span K {w} ↔ _
  refine (hew (baseActionEquiv M g)).trans ⟨?_, ?_⟩
  · intro he
    apply (hS g).mp
    intro f hf
    let m : M := ⟨f, hFM hf⟩
    have hm : m ∈ N := hf
    have ht : baseActionEquiv M g m ∈ N := by
      rw [← he]
      exact Submodule.mem_map_of_mem hm
    change ((Comodule.basePointsRepresentation (R := K) (H := H) M g m : M) : H) ∈ F at ht
    rw [base_action_coe] at ht
    exact ht
  · intro hg
    apply Submodule.eq_of_le_of_finrank_eq ?_ ((baseActionEquiv M g).finrank_map_eq N)
    rintro m' ⟨m, hm, rfl⟩
    change ((Comodule.basePointsRepresentation (R := K) (H := H) M g m : M) : H) ∈ F
    rw [base_action_coe]
    exact (hS g).mpr hg m hm

end GroupActions
