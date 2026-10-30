import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneReflectionTransport
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneConjugation

/-! # Chosen character reflections and their conjugation on root subgroups -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u

section Generic

variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)

/-- The adjoint action of a product is the composite of the adjoint actions. -/
theorem AffineGroupAdjointLieEquiv.mul_toLinearMap (g h : WithConv (B →ₐ[K] K)) :
    ((affineGroupAdjointLieEquiv (g * h)).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
      ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤).comp
        ((affineGroupAdjointLieEquiv h).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) := by
  apply LinearMap.ext
  intro v
  change affineGroupAdjointRepresentation (g * h) v =
    affineGroupAdjointRepresentation g (affineGroupAdjointRepresentation h v)
  rw [map_mul, Module.End.mul_apply]

/-- The identity point acts trivially on the tangent algebra. -/
theorem AffineGroupAdjointLieEquiv.one_toLinearMap :
    ((affineGroupAdjointLieEquiv (1 : WithConv (B →ₐ[K] K))).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  change affineGroupAdjointRepresentation (1 : WithConv (B →ₐ[K] K)) v = v
  rw [map_one, Module.End.one_apply]

/-- Transport of an indexed family of subspaces by the identity point. -/
theorem affineGroupAdjoint_transport_one {ρ : Type*} (V : ρ → Submodule K 𝔤) (r : ρ) :
    (V r).map ((affineGroupAdjointLieEquiv (1 : WithConv (B →ₐ[K] K))).toLinearEquiv :
      𝔤 →ₗ[K] 𝔤) = V ((1 : Equiv.Perm ρ) r) := by
  rw [AffineGroupAdjointLieEquiv.one_toLinearMap, Submodule.map_id, Equiv.Perm.one_apply]

/-- Transport of an indexed family of subspaces is multiplicative. -/
theorem affineGroupAdjoint_transport_mul {ρ : Type*} (V : ρ → Submodule K 𝔤)
    (g h : WithConv (B →ₐ[K] K)) (σ τ : Equiv.Perm ρ)
    (hg : ∀ r, (V r).map ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) = V (σ r))
    (hh : ∀ r, (V r).map ((affineGroupAdjointLieEquiv h).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) = V (τ r))
    (r : ρ) :
    (V r).map ((affineGroupAdjointLieEquiv (g * h)).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
      V ((σ * τ) r) := by
  rw [AffineGroupAdjointLieEquiv.mul_toLinearMap, Submodule.map_comp, hh r, hg (τ r),
    Equiv.Perm.mul_apply]

end Generic

variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- A chosen `sl₂`-normalized pair `(x_α, y_α)` for every occurring
nonidentity character `α` of the maximal torus
(`exists_isRootSl2Pair`). -/
def characterSl2PairChoice
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    (B →ₐc[K] SymmetricAlgebra K K) × (B →ₐc[K] SymmetricAlgebra K K) :=
  (Classical.choose (exists_isRootSl2Pair I hI π hπ hker hB α.val α.property.1 α.property.2),
    Classical.choose (Classical.choose_spec
      (exists_isRootSl2Pair I hI π hπ hker hB α.val α.property.1 α.property.2)))

/-- The chosen pair is `sl₂`-normalized for `α`. -/
theorem characterSl2PairChoice_isRootSl2Pair
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    IsRootSl2Pair π α.val (characterSl2PairChoice I hI π hπ hker hB α).1
      (characterSl2PairChoice I hI π hπ hker hB α).2 :=
  Classical.choose_spec (Classical.choose_spec
    (exists_isRootSl2Pair I hI π hπ hker hB α.val α.property.1 α.property.2))

/-- The reflection point `n_α = x_α(1) y_α(-1) x_α(1)` of the chosen pair. -/
def characterReflectionPoint
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    WithConv (B →ₐ[K] K) :=
  rootReflectionPoint (characterSl2PairChoice I hI π hπ hker hB α).1
    (characterSl2PairChoice I hI π hπ hker hB α).2

omit [Finite ι] in
/-- If `Ad(g)` maps the `α` character space onto the `β` character space with
`β ≠ 1`, then `g` conjugates the points of every `Ga` subgroup with tangent in
the `α` space to the points of the `Ga` subgroup with tangent
`Ad(g)(dz)`, which lies in the `β` space. -/
theorem ga_conjugation_of_characterSpace_map
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K)) (α β : M) (hβ : β ≠ 1)
    (hmap : (affineGroupCharacterWeightSpace π α).map
        ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
      affineGroupCharacterWeightSpace π β)
    (z : B →ₐc[K] SymmetricAlgebra K K)
    (hz : gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π α) :
    ∃ z' : B →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupTangent z' = affineGroupAdjointRepresentation g (gaAffineGroupTangent z) ∧
      gaAffineGroupTangent z' ∈ affineGroupCharacterWeightSpace π β ∧
      ∀ u : K, g * gaAffineGroupPoints z (Multiplicative.ofAdd u) * g⁻¹ =
        gaAffineGroupPoints z' (Multiplicative.ofAdd u) := by
  have hd : affineGroupAdjointRepresentation g (gaAffineGroupTangent z) ∈
      affineGroupCharacterWeightSpace π β := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hz
  obtain ⟨z', hz', _⟩ := CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ β hβ _
    hd
  refine ⟨z', hz', hz' ▸ hd, fun u => ?_⟩
  have htan : affineGroupAdjointRepresentation g (gaAffineGroupTangent z) =
      (1 : K) • gaAffineGroupTangent z' := by
    rw [hz', one_smul]
  simpa only [one_mul] using GaAffineGroupPoints.conjugate_of_tangent_eq z z' g 1 htan u

/-- **Scaled root-subgroup conjugation.** In the original reductive group, if
`Ad(g)` maps the `α` character space onto the occurring nonidentity `β`
character space, then for `Ga` morphisms `z, z'` with nonzero tangents in the
`α` and `β` spaces there is `c ≠ 0` with `g z(u) g⁻¹ = z'(c u)` for all `u`. -/
theorem WeylRepresentativeReflections.conjugation_scaled_of_characterSpace_map
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (g : WithConv (B →ₐ[K] K)) (α β : M) (hβ : β ≠ 1)
    (hβocc : affineGroupCharacterWeightSpace π β ≠ ⊥)
    (hmap : (affineGroupCharacterWeightSpace π α).map
        ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
      affineGroupCharacterWeightSpace π β)
    (z z' : B →ₐc[K] SymmetricAlgebra K K)
    (hz : gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π α)
    (hz0 : gaAffineGroupTangent z ≠ 0)
    (hz' : gaAffineGroupTangent z' ∈ affineGroupCharacterWeightSpace π β)
    (hz'0 : gaAffineGroupTangent z' ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ u : K,
      g * gaAffineGroupPoints z (Multiplicative.ofAdd u) * g⁻¹ =
        gaAffineGroupPoints z' (Multiplicative.ofAdd (c * u)) := by
  have hd : affineGroupAdjointRepresentation g (gaAffineGroupTangent z) ∈
      affineGroupCharacterWeightSpace π β := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hz
  have hfin := ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB β hβ
    hβocc
  have h0 : (⟨gaAffineGroupTangent z', hz'⟩ : affineGroupCharacterWeightSpace π β) ≠ 0 := by
    intro h
    exact hz'0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h0).mp hfin ⟨_, hd⟩
  have hcx : affineGroupAdjointRepresentation g (gaAffineGroupTangent z) =
      c • gaAffineGroupTangent z' := (congrArg Subtype.val hc).symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    apply hz0
    apply (affineGroupAdjointLieEquiv g).injective
    exact (congrArg Subtype.val hc).symm.trans (map_zero _).symm
  exact ⟨c, hc0, GaAffineGroupPoints.conjugate_of_tangent_eq z z' g c hcx⟩

end ReductiveGroups
