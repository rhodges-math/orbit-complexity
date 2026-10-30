import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.LeftTangentOperator
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent
import OrbitComplexity.ReductiveGroups.Lie.Roots.JordanInvariantSubmodule

/-!
# Tangent Jordan Kernel

Transfer of finite-dimensional Jordan information to the tangent of the
original closed subgroup. The finite-restriction hypotheses are explicit;
they are verified for matrix Jordan parts in `Groups/AlgebraicTangentJordan.lean`. -/

noncomputable section
namespace ReductiveGroups

variable {K A B : Type*} [Field K] [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]

/-- An ambient tangent belongs to the subgroup tangent if and only if
its invariant coordinate operator preserves the original defining kernel. -/
theorem TangentJordanKernel.iff_leftTangentOperator_preserves_kernel
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K) ρ).range ↔
      LinearMap.ker ρ.toLinearMap ∈ (leftTangentOperator d).invtSubmodule := by
  constructor
  · rintro ⟨e, rfl⟩ a ha
    exact leftTangentOperator_preserves_kernel ρ e a ha
  · intro h
    apply (tangent_mem_range_iff_kills_kernel ρ hρ d).mpr
    intro a ha
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K A K).injective
    rw [map_zero]
    change scalarTangentLinear d a = 0
    rw [← counit_leftTangentOperator]
    have hz : ρ (leftTangentOperator d a) = 0 := h ha
    have hco := DFunLike.congr_fun (BialgHom.counitAlgHom_comp ρ)
      (leftTangentOperator d a)
    change Coalgebra.counit (R := K) (ρ (leftTangentOperator d a)) =
      Coalgebra.counit (R := K) (leftTangentOperator d a) at hco
    rw [hz, map_zero] at hco
    exact hco.symm

/-- Once the coordinate operators form a Jordan decomposition on
finite invariant spaces exhausting the coordinate algebra, both ambient
tangents descend to the original closed subgroup. No group reductivity is
required by this descent step. -/
theorem TangentJordanKernel.mem_range_of_finite_jordan_restrictions [PerfectField K]
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (d n s : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K))
    (hd : d ∈ (TauCeti.derivationCompLieHom (B := K) ρ).range)
    (hcomm : Commute (leftTangentOperator n) (leftTangentOperator s))
    (hsum : leftTangentOperator d = leftTangentOperator n + leftTangentOperator s)
    (hlocal : ∀ a : A, ∃ W : Submodule K A, ∃ _ : FiniteDimensional K W,
      ∃ hnW : W ∈ (leftTangentOperator n).invtSubmodule,
      ∃ hsW : W ∈ (leftTangentOperator s).invtSubmodule,
        a ∈ W ∧ IsNilpotent ((leftTangentOperator n).restrict hnW) ∧
          Module.End.IsSemisimple ((leftTangentOperator s).restrict hsW)) :
    n ∈ (TauCeti.derivationCompLieHom (B := K) ρ).range ∧
      s ∈ (TauCeti.derivationCompLieHom (B := K) ρ).range := by
  have hker := (TangentJordanKernel.iff_leftTangentOperator_preserves_kernel ρ hρ d).mp hd
  have hparts (a : A) (ha : a ∈ LinearMap.ker ρ.toLinearMap) :
      leftTangentOperator n a ∈ LinearMap.ker ρ.toLinearMap ∧
        leftTangentOperator s a ∈ LinearMap.ker ρ.toLinearMap := by
    obtain ⟨W, hfin, hnW, hsW, haW, hn, hs⟩ := hlocal a
    let := hfin
    exact invariantSubmodule_jordanParts_at hcomm hsum hker hnW hsW hn hs ha haW
  constructor
  · apply (TangentJordanKernel.iff_leftTangentOperator_preserves_kernel ρ hρ n).mpr
    intro a ha
    exact (hparts a ha).1
  · apply (TangentJordanKernel.iff_leftTangentOperator_preserves_kernel ρ hρ s).mpr
    intro a ha
    exact (hparts a ha).2

end ReductiveGroups
