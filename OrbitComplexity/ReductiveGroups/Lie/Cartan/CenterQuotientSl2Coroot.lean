import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalRootEigenvectors

/-!
# Center Quotient Sl 2 Coroot

The bracket element of an original root sl2 triple maps to the
coroot in the Killing quotient. This identifies the normalization
needed to compare original group reflections with the root-system Weyl group. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.HasCentralRadical K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

local instance : LieAlgebra.IsKilling K (L ⧸ center K L) :=
  centralRadical_centerQuotient_isKilling

local instance : (centerQuotientCartan H).IsCartanSubalgebra := by
  apply cartan_map_of_surjective (centerQuotientLieHom (K := K) (L := L))
    centerQuotientLieHom_surjective H
  rw [centerQuotientLieHom_ker]
  exact center_le_cartan H

/-- No central ambiguity remains after passage to the center
quotient: the h in an original root-positioned sl2 triple maps to its coroot. -/
theorem centerQuotient_sl2_h_eq_coroot
    (χ : Weight K H L) (hχ : χ.IsNonZero)
    {h e f : L} (hs : IsSl2Triple h e f)
    (he : e ∈ rootSpace H χ) (hf : f ∈ rootSpace H (-(χ : H → K)))
    (hh : h ∈ H) :
    centerQuotientLieHom (K := K) h =
      (coroot (centerQuotientWeightOfNonZero H χ hχ) : L ⧸ center K L) := by
  let q := centerQuotientLieHom (K := K) (L := L)
  let ψ := centerQuotientWeightOfNonZero H χ hχ
  have hψ : ψ.IsNonZero := by
    intro hz
    exact centerQuotientWeightDescent_ne_zero H χ hχ (DFunLike.coe_injective hz)
  have heval : (fun t : H => ψ (centerQuotientCartanMap H t)) = (χ : H → K) := by
    funext t
    exact centerQuotientWeightOfNonZero_apply_map H χ hχ t
  have he' : e ∈ rootSpace H (fun t => ψ (centerQuotientCartanMap H t)) := by
    rw [heval]
    exact he
  have hf' : f ∈ rootSpace H (fun t => (-ψ) (centerQuotientCartanMap H t)) := by
    change f ∈ rootSpace H (-(fun t : H => ψ (centerQuotientCartanMap H t)))
    rw [heval]
    exact hf
  have hqe : q e ∈ rootSpace (centerQuotientCartan H) ψ :=
    (centerQuotientRootSpaceMap H (ψ : centerQuotientCartan H → K) ⟨e, he'⟩).property
  have hqf : q f ∈ rootSpace (centerQuotientCartan H) (-ψ) :=
    (centerQuotientRootSpaceMap H ((-ψ) : centerQuotientCartan H → K) ⟨f, hf'⟩).property
  have hqh : q h ≠ 0 := by
    intro hz
    have hm : centerQuotientCartanMap H ⟨h, hh⟩ = 0 := Subtype.ext hz
    have hv : ψ (centerQuotientCartanMap H ⟨h, hh⟩) = χ ⟨h, hh⟩ :=
      centerQuotientWeightOfNonZero_apply_map H χ hχ ⟨h, hh⟩
    have hzero : ψ 0 = 0 := map_zero ψ.toLinear
    rw [hm, hzero] at hv
    have ht := centralRadical_sl2_root_apply_eq_two H χ hχ hs he hh
    exact (two_ne_zero : (2 : K) ≠ 0) (ht.symm.trans hv.symm)
  have hsq : IsSl2Triple (q h) (q e) (q f) := {
    h_ne_zero := hqh
    lie_e_f := by rw [← LieHom.map_lie, hs.lie_e_f]
    lie_h_e_nsmul := by rw [← LieHom.map_lie, hs.lie_h_e_nsmul, map_nsmul]
    lie_h_f_nsmul := by rw [← LieHom.map_lie, hs.lie_h_f_nsmul, map_neg, map_nsmul] }
  exact hsq.h_eq_coroot hψ hqe hqf

end ReductiveGroups
