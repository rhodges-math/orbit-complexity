import OrbitComplexity.ReductiveGroups.Groups.Characters.AffineGroupCharacterWeights
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointFirstOrder

/-!
# Character Weight Differential

Differentiating the diagonalizable-group adjoint character action. -/

noncomputable section
namespace ReductiveGroups

open WithConv
open scoped TensorProduct

universe u
variable {K B M : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CommGroup M]

private abbrev C (A : Type u) :=
  TauCeti.Bialgebra.CounitAlgebra K A K

private abbrev D := DualNumber (C (K := K) B)

/-- The character weight equation differentiated at a dual-number torus point. -/
theorem bracket_eq_character_derivative
    (π : B →ₐc[K] MonoidAlgebra K M) (α : M)
    (h : Derivation K (MonoidAlgebra K M) (C (K := K) (MonoidAlgebra K M)))
    (d : Derivation K B (C (K := K) B))
    (hd : d ∈ affineGroupCharacterWeightSpace π α) :
    ⁅TauCeti.derivationComp (B := K) π h, d⁆ =
      ((TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K)
        (h (MonoidAlgebra.single α 1))) • d := by
  let hB := TauCeti.derivationComp (B := K) π h
  let f := (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm d
  have hf : f ∈ Derivation.adjointWeightSpace π α := hd
  let q : WithConv (MonoidAlgebra K M →ₐ[K] D (K := K) (B := B)) :=
    tangentDualPoint h
  have hw := Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace
    π q.ofConv (1 : D (K := K) (B := B)) hf
  have hc := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (CommAlgCat.of K (D (K := K) (B := B)))
    (TauCeti.AlgHom.mapDomain π q) (1 ⊗ₜ[K] f)
  have hq : TauCeti.AlgHom.mapDomain π q = tangentDualPoint hB := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · change TrivSqZeroExt.fst (q.ofConv (π b)) =
        TrivSqZeroExt.fst ((tangentDualPoint hB).ofConv b)
      change TrivSqZeroExt.fst ((tangentDualPoint h).ofConv (π b)) =
        TrivSqZeroExt.fst ((tangentDualPoint hB).ofConv b)
      rw [tangentDualPoint_fst, tangentDualPoint_fst]
      rw [TauCeti.Bialgebra.CounitAlgebra.algebraMap_apply,
        TauCeti.Bialgebra.CounitAlgebra.algebraMap_apply]
      exact congrArg (algebraMap K K)
        (DFunLike.congr_fun (BialgHom.counitAlgHom_comp π) b)
    · change TrivSqZeroExt.snd (q.ofConv (π b)) =
        TrivSqZeroExt.snd ((tangentDualPoint hB).ofConv b)
      change TrivSqZeroExt.snd ((tangentDualPoint h).ofConv (π b)) =
        TrivSqZeroExt.snd ((tangentDualPoint hB).ofConv b)
      rw [tangentDualPoint_snd, tangentDualPoint_snd]
      exact (TauCeti.derivationComp_apply π h b).symm
  have hb : Derivation.tangentScalarExtensionEquiv (R := K) (A := B)
      (B := D (K := K) (B := B)) (1 ⊗ₜ[K] f) = baseDualDerivation d := by
    ext b
    rw [Derivation.tangentScalarExtensionEquiv_tmul_apply]
    have hfval : f (TauCeti.Bialgebra.cotangentMap K B b) = d b := by
      rw [← Derivation.cotangentLinearEquiv_apply_apply]
      exact congrArg (fun z : Derivation K B (C (K := K) B) => z b)
        ((Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).apply_symm_apply d)
    rw [hfval, one_mul]
    change (algebraMap K (D (K := K) (B := B))) (d b) =
      (baseDualDerivation d) b
    change TrivSqZeroExt.inl (d b) =
      (Derivation.mapValue (Algebra.ofId K (D (K := K) (B := B))) d) b
    rw [Derivation.mapValue_apply]
    rfl
  have hp : Derivation.pointInCounitAlgebra (D (K := K) (B := B))
      (TauCeti.AlgHom.mapDomain π q) = tangentDualPoint hB := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    change (Derivation.pointInCounitAlgebra (D (K := K) (B := B))
      (TauCeti.AlgHom.mapDomain π q)).ofConv b =
      (tangentDualPoint hB).ofConv b
    rw [Derivation.pointInCounitAlgebra_apply, hq]
  have heq : Derivation.tangentScalarExtensionEquiv (R := K) (A := B)
      (B := D (K := K) (B := B))
        ((q.ofConv (MonoidAlgebra.single α 1)) ⊗ₜ[K] f) =
      tangentDualAdjoint hB d := by
    have hmap : (TauCeti.AlgHom.mapDomain π q).ofConv =
        q.ofConv.comp (π : B →ₐ[K] MonoidAlgebra K M) := rfl
    rw [hmap, hw, one_mul, hb, hp] at hc
    exact hc
  apply Derivation.ext
  intro b
  have hv := congrArg (fun z : Derivation K B
      (TauCeti.Bialgebra.CounitAlgebra K B (D (K := K) (B := B))) =>
        TrivSqZeroExt.snd (z b)) heq
  rw [Derivation.tangentScalarExtensionEquiv_tmul_apply,
    tangentDualAdjoint_snd] at hv
  have hfval : f (TauCeti.Bialgebra.cotangentMap K B b) = d b := by
    rw [← Derivation.cotangentLinearEquiv_apply_apply]
    exact congrArg (fun z : Derivation K B (C (K := K) B) => z b)
      ((Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).apply_symm_apply d)
  rw [hfval] at hv
  change TrivSqZeroExt.snd
    (q.ofConv (MonoidAlgebra.single α 1) *
      (TrivSqZeroExt.inl (d b) : D (K := K) (B := B))) = ⁅hB, d⁆ b at hv
  rw [DualNumber.snd_mul] at hv
  simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, mul_zero] at hv
  have hqsnd : TrivSqZeroExt.snd (q.ofConv (MonoidAlgebra.single α 1)) =
      h (MonoidAlgebra.single α 1) := tangentDualPoint_snd h _
  rw [hqsnd] at hv
  simp only [zero_add] at hv
  rw [← hv]
  change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K
      (h (MonoidAlgebra.single α 1))) *
      (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K (d b)) =
    ((TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K)
      (h (MonoidAlgebra.single α 1)) • d) b
  exact (TauCeti.algEquivSelf_derivation_smul_apply _ d b).symm

end ReductiveGroups
