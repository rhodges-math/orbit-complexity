import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalRootSl2
import OrbitComplexity.ReductiveGroups.Lie.Roots.Sl2AdjointReflection

/-!
# Central Radical Root Eigenvectors

Exact eigenvector brackets for nonzero roots in a reductive Lie algebra. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.HasCentralRadical K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-- A nonzero root vector is an eigenvector for the original Cartan
action. The Killing argument takes place only in the center quotient. -/
theorem CentralRadical.lie_eq_smul_of_mem_rootSpace
    (χ : Weight K H L) (hχ : χ.IsNonZero) {x : L}
    (hx : x ∈ rootSpace H χ) (t : H) :
    ⁅(t : L), x⁆ = χ t • x := by
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
  have heval : (fun u : H => ψ (centerQuotientCartanMap H u)) = (χ : H → K) := by
    funext u
    exact centerQuotientWeightOfNonZero_apply_map H χ hχ u
  have hx' : x ∈ rootSpace H
      (fun u : H => ψ (centerQuotientCartanMap H u)) := by
    rw [heval]
    exact hx
  let x' : rootSpace H (fun u : H => ψ (centerQuotientCartanMap H u)) := ⟨x, hx'⟩
  have hqx : q x ∈ rootSpace (centerQuotientCartan H) ψ :=
    (centerQuotientRootSpaceMap H (ψ : centerQuotientCartan H → K) x').property
  have hqt : ⁅(centerQuotientCartanMap H t : L ⧸ LieAlgebra.center K L), q x⁆ =
      ψ (centerQuotientCartanMap H t) • q x :=
    LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace hqx (centerQuotientCartanMap H t)
  have ht0 : (t : L) ∈ rootSpace H (0 : H → K) :=
    toLieSubmodule_le_rootSpace_zero K L H t.property
  have hmem : ⁅(t : L), x⁆ ∈ rootSpace H χ := by
    have hz := lie_mem_genWeightSpace_of_mem_genWeightSpace ht0 hx
    simpa only [zero_add] using hz
  have hEq : (⟨⁅(t : L), x⁆, hmem⟩ : rootSpace H χ) =
      (⟨χ t • x, (rootSpace H χ).smul_mem _ hx⟩ : rootSpace H χ) :=
    centerQuotient_injective_on_rootSpace H (χ : H → K) hχ (by
      change q ⁅(t : L), x⁆ = q (χ t • x)
      rw [LieHom.map_lie, map_smul]
      change ⁅(centerQuotientCartanMap H t : L ⧸ LieAlgebra.center K L), q x⁆ =
        χ t • q x
      rw [← centerQuotientWeightOfNonZero_apply_map H χ hχ t]
      exact hqt)
  exact congrArg Subtype.val hEq

/-- The bracket element in any nonzero-root `sl₂` triple has root
value two. -/
theorem centralRadical_sl2_root_apply_eq_two
    (χ : Weight K H L) (hχ : χ.IsNonZero)
    {h e f : L} (hs : IsSl2Triple h e f)
    (he : e ∈ rootSpace H χ) (hh : h ∈ H) :
    χ (⟨h, hh⟩ : H) = 2 := by
  have hbr := CentralRadical.lie_eq_smul_of_mem_rootSpace H χ hχ he
    (⟨h, hh⟩ : H)
  rw [hs.lie_h_e_smul K] at hbr
  exact smul_left_injective K hs.e_ne_zero hbr.symm

/-- The rank-one adjoint reflection on the original Cartan, once the two
adjoint operators are known nilpotent. -/
theorem centralRadical_sl2_adjoint_reflection
    (χ : Weight K H L) (hχ : χ.IsNonZero)
    {h e f : L} (hs : IsSl2Triple h e f)
    (he : e ∈ rootSpace H χ)
    (hf : f ∈ rootSpace H (-(χ : H → K)))
    (hne : IsNilpotent (ad K L e))
    (hfn : IsNilpotent (ad K L (-f))) (t : H) :
    nilpotentAdjointExponential e hne
      (nilpotentAdjointExponential (-f) hfn
        (nilpotentAdjointExponential e hne (t : L))) =
      (t : L) - χ t • h := by
  let χneg : Weight K H L := ⟨-(χ : H → K), by
    intro hz
    have hzero : f = 0 :=
      (LieSubmodule.eq_bot_iff (N := rootSpace H (-(χ : H → K)))).mp hz f hf
    exact hs.f_ne_zero hzero⟩
  have hχneg : χneg.IsNonZero := by
    change (-(χ : H → K)) ≠ 0
    simpa using hχ
  have hte : ⁅(t : L), e⁆ = χ t • e :=
    CentralRadical.lie_eq_smul_of_mem_rootSpace H χ hχ he t
  have htf : ⁅(t : L), f⁆ = (-χ t) • f := by
    simpa only [χneg, Weight.coe_weight_mk, Pi.neg_apply] using
      CentralRadical.lie_eq_smul_of_mem_rootSpace H χneg hχneg hf t
  exact sl2_adjoint_reflection h e f (t : L) (χ t) hs hne hfn hte htf

end ReductiveGroups
