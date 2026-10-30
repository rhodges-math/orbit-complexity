import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalRootMultiplicity
import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Central Radical Root Sl 2

Lift a rank-one triple from the center quotient of a reductive Lie algebra. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.HasCentralRadical K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-- A nonzero original root admits an `sl₂` triple in the original
reductive Lie algebra. Killing nondegeneracy is used only in its center quotient. -/
theorem centralRadical_exists_isSl2Triple
    (χ : Weight K H L) (hχ : χ.IsNonZero) :
    ∃ h e f : L, IsSl2Triple h e f ∧
      e ∈ rootSpace H χ ∧ f ∈ rootSpace H (-(χ : H → K)) ∧ h ∈ H := by
  let q := centerQuotientLieHom (K := K) (L := L)
  let _ := centralRadical_centerQuotient_isKilling (K := K) (L := L)
  have hker : (q.ker : LieSubalgebra K L) ≤ H := by
    change (centerQuotientLieHom (K := K) (L := L)).ker ≤ H
    rw [centerQuotientLieHom_ker]
    exact center_le_cartan H
  let _ := cartan_map_of_surjective q centerQuotientLieHom_surjective H hker
  let ψ := centerQuotientWeightOfNonZero H χ hχ
  have hψ : ψ.IsNonZero := by
    intro hz
    apply centerQuotientWeightDescent_ne_zero H χ hχ
    exact DFunLike.coe_injective hz
  obtain ⟨hq, eq, fq, hs, heq, hfq⟩ :=
    exists_isSl2Triple_of_weight_isNonZero hψ
  have heval : (fun u : H => ψ (centerQuotientCartanMap H u)) = (χ : H → K) := by
    funext u
    exact centerQuotientWeightOfNonZero_apply_map H χ hχ u
  have hnegψ : (-(ψ : centerQuotientCartan H → K)) ≠ 0 := by
    simpa using hψ
  let e0 := (centerQuotientRootSpaceEquiv H (ψ : centerQuotientCartan H → K) hψ).symm
    (⟨eq, heq⟩ : rootSpace (centerQuotientCartan H) ψ)
  let f0 := (centerQuotientRootSpaceEquiv H
    (-(ψ : centerQuotientCartan H → K)) hnegψ).symm
    (⟨fq, hfq⟩ : rootSpace (centerQuotientCartan H) (-(ψ : centerQuotientCartan H → K)))
  let e : L := e0
  let f : L := f0
  have he : e ∈ rootSpace H χ := by
    rw [← heval]
    exact e0.property
  have hf : f ∈ rootSpace H (-(χ : H → K)) := by
    have hneg : (fun u : H => (-(ψ : centerQuotientCartan H → K))
        (centerQuotientCartanMap H u)) = -(χ : H → K) := by
      funext u
      simpa only [Pi.neg_apply] using congrArg Neg.neg (congrFun heval u)
    rw [← hneg]
    exact f0.property
  have hqe : q e = eq := by
    simpa only [e, e0, LinearEquiv.apply_symm_apply] using
      centerQuotientRootSpaceEquiv_apply H
        (ψ : centerQuotientCartan H → K) hψ e0 |>.symm
  have hqf : q f = fq := by
    simpa only [f, f0, LinearEquiv.apply_symm_apply] using
      centerQuotientRootSpaceEquiv_apply H
        (-(ψ : centerQuotientCartan H → K)) hnegψ f0 |>.symm
  let h : L := ⁅e, f⁆
  have hh0 : h ∈ rootSpace H (0 : H → K) := by
    let e' : rootSpace H χ := ⟨e, he⟩
    let f' : rootSpace H (-(χ : H → K)) := ⟨f, hf⟩
    have hz := (rootSpaceProduct K L H (χ : H → K) (-(χ : H → K))
      0 (add_neg_cancel (χ : H → K))
      (e' ⊗ₜ[K] f')).property
    simpa only [h, rootSpaceProduct_tmul] using hz
  have hh : h ∈ H := by
    simpa only [rootSpace_zero_eq K L H, LieSubalgebra.mem_toLieSubmodule] using hh0
  have hqh : q h = hq := by
    change q ⁅e, f⁆ = hq
    rw [LieHom.map_lie, hqe, hqf, hs.lie_e_f]
  have hne : h ≠ 0 := by
    intro hz
    apply hs.h_ne_zero
    simpa [hz] using hqh.symm
  have hhe : ⁅h, e⁆ = (2 : K) • e := by
    have hmem : ⁅h, e⁆ ∈ rootSpace H χ := by
      have hz := lie_mem_genWeightSpace_of_mem_genWeightSpace hh0 he
      simpa only [zero_add] using hz
    have hEq : (⟨⁅h,e⁆,hmem⟩ : rootSpace H χ) =
        (⟨(2:K) • e,(rootSpace H χ).smul_mem _ he⟩ : rootSpace H χ) :=
      centerQuotient_injective_on_rootSpace H (χ : H → K) hχ (by
        change q ⁅h,e⁆ = q ((2:K) • e)
        rw [LieHom.map_lie, map_smul, hqh, hqe, hs.lie_h_e_smul K])
    exact congrArg Subtype.val hEq
  have hhf : ⁅h, f⁆ = -((2 : K) • f) := by
    have hmem : ⁅h, f⁆ ∈ rootSpace H (-(χ : H → K)) := by
      have hz := lie_mem_genWeightSpace_of_mem_genWeightSpace hh0 hf
      simpa only [zero_add] using hz
    have hnegχ : (-(χ : H → K)) ≠ 0 := by
      simpa using hχ
    have hEq : (⟨⁅h,f⁆,hmem⟩ : rootSpace H (-(χ : H → K))) =
        (⟨-((2:K) • f),(rootSpace H (-(χ : H → K))).neg_mem
          ((rootSpace H (-(χ : H → K))).smul_mem _ hf)⟩ :
          rootSpace H (-(χ : H → K))) :=
      centerQuotient_injective_on_rootSpace H (-(χ : H → K)) hnegχ (by
        change q ⁅h,f⁆ = q (-((2:K) • f))
        rw [LieHom.map_lie, map_neg, map_smul, hqh, hqf, hs.lie_lie_smul_f K])
    exact congrArg Subtype.val hEq
  exact ⟨h, e, f, ⟨hne, rfl, by simpa [two_smul] using hhe,
    by simpa [two_smul] using hhf⟩, he, hf, hh⟩

end ReductiveGroups
