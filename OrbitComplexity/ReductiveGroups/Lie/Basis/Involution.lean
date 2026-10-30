import OrbitComplexity.ReductiveGroups.Lie.Basis.Equivalence

/-! # Cartan-inverting automorphisms of based Killing algebras -/

noncomputable section

namespace ReductiveGroups.LieBasis

open LieSubalgebra Set

universe u v w
variable {K : Type u} {L : Type v} {ι : Type w}
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L] [Finite ι]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable K H L]

/-- A split Killing algebra has an involution negating its Cartan subalgebra
and exchanging the two generator families of a basis. -/
theorem exists_cartan_involution (b : LieAlgebra.Basis ι H) :
    ∃ ω : L ≃ₗ⁅K⁆ L, (∀ h : H, ω (h : L) = -(h : L)) ∧
      (∀ i, ω (b.e i) = b.f i ∧ ω (b.f i) = b.e i) ∧ Function.Involutive ω := by
  have hA : b.A.reindex (Equiv.refl ι) (Equiv.refl ι) = b.symm.A := by
    ext i j
    rfl
  let ω := equivOfKilling (Equiv.refl ι) b b.symm hA
  have hh (i : ι) : ω (b.h i) = -b.h i :=
    equivOfKilling_h (Equiv.refl ι) b b.symm hA i
  have he (i : ι) : ω (b.e i) = b.f i :=
    equivOfKilling_e (Equiv.refl ι) b b.symm hA i
  have hf (i : ι) : ω (b.f i) = b.e i :=
    equivOfKilling_f (Equiv.refl ι) b b.symm hA i
  refine ⟨ω, ?_, fun i => ⟨he i, hf i⟩, ?_⟩
  · intro h
    have hp (x : L) (hx : x ∈ Submodule.span K (range b.h)) : ω x = -x := by
      induction hx using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨i, rfl⟩ := ha
        exact hh i
      | zero => simp only [map_zero, neg_zero]
      | add a c _ _ ha hc =>
        rw [map_add, ha, hc, neg_add]
      | smul t a _ ha =>
        rw [map_smul, ha, smul_neg]
    apply hp
    rw [← b.coe_cartan_eq_span]
    exact h.property
  · intro z
    have hz : z ∈ lieSpan K L (range b.e ∪ range b.f) := by
      rw [b.span_ef]
      trivial
    induction hz using lieSpan_induction with
    | mem a ha =>
      rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [he, hf]
      · rw [hf, he]
    | zero => simp only [map_zero]
    | add a c _ _ ha hc => rw [map_add, map_add, ha, hc]
    | smul t a _ ha => rw [map_smul, map_smul, ha]
    | lie a c _ _ ha hc => rw [ω.map_lie, ω.map_lie, ha, hc]

end ReductiveGroups.LieBasis
