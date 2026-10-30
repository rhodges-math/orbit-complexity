import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneReflection
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootReflectionConjugation

/-!
# Root Rank One Reflection Transport

Root-space transport by the reflection point of an arbitrary
`sl₂`-normalized pair.

In the original reductive group, let `(x, y)` be an `sl₂`-normalized pair for
an occurring nonidentity character `α`, and `n = x(1) y(-1) x(1)`. The bracket
`⁅dx, dy⁆` maps to the coroot of the corresponding root of the center
quotient, so `Ad(n)` acts on the torus tangent image by the standard
coreflection. Consequently, for every occurring nonidentity character `β`,
`Ad(n)` maps the `β` character space onto the space of the character
`s_α(β) := E⁻¹ (reflectionPerm (E α) (E β))`, where
`E = ReductiveGroups.ReductiveCharacterRoots.characterCenterQuotientRootEquiv` is the proved
correspondence
between original nonidentity characters and roots of the center quotient and
`reflectionPerm` is Mathlib's root-system reflection permutation. Conjugation by
`n` carries the points of every `Ga` subgroup with tangent in the `β` space to
the points of the `Ga` subgroup with tangent `Ad(n)(dz)`, parameter by
parameter. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The reflection of a quotient root evaluates after the matching Cartan
coreflection as the original root. -/
private theorem RankOne.reflection_coreflection
    {L : Type u} [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieAlgebra.IsKilling K L]
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (α β : H.root) (t : H) :
    ((rootSystem H).reflectionPerm α β).val
      ((rootSystem H).coreflection α t) = β.val t := by
  let P := rootSystem H
  change (P.root (P.reflectionPerm α β)) (P.coreflection α t) = P.root β t
  rw [P.root_reflectionPerm]
  have h := congrArg
    (fun F : H →ₗ[K] Module.Dual K (Module.Dual K H) =>
      F (P.coreflection α t) (P.root β))
    (P.reflection_dualMap_eq_coreflection α)
  simpa [P, LinearEquiv.dualMap_apply, LinearMap.dualMap_apply,
    P.coreflection_same] using h

set_option maxHeartbeats 400000 in
/-- The reflection point of an `sl₂`-normalized pair for `α` maps every vector
of the `β` character space into the `s_α(β)` character space, for every
occurring nonidentity `β`. -/
theorem IsRootSl2Pair.rootReflectionPoint_characterSpace_mem
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1})
    {x y : B →ₐc[K] SymmetricAlgebra K K} (hp : IsRootSl2Pair π α.val x y) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ∀ β : {β : M // affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
      ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π β.val →
        affineGroupAdjointRepresentation (rootReflectionPoint x y) d ∈
          affineGroupCharacterWeightSpace π
            (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
              (E α) (E β))).val := by
  intro _ _ _ _ _ H E
  let P := rootSystem (centerQuotientCartan H)
  let g := rootReflectionPoint x y
  let h : H := ⟨_, hp.bracket_mem⟩
  let χs := nonidentityCharacterLieWeightEquiv π hπ α
  have hχ : (χs.val : H → K) = characterDifferentialOnImage π hπ α.val := by
    funext t
    exact nonidentityCharacterLieWeightEquiv_apply π hπ α t
  have he : gaAffineGroupTangent x ∈ rootSpace H χs.val := by
    have hm := hp.tangent_mem
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α.val, ← hχ] at hm
    exact hm
  have hf : gaAffineGroupTangent y ∈ rootSpace H (-(χs.val : H → K)) := by
    have hm := hp.partner_tangent_mem
    have hneg : (characterDifferentialOnImage π hπ α.val⁻¹ : H → K) =
        -(χs.val : H → K) := by
      rw [characterDifferentialOnImage_inv, hχ]
      rfl
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α.val⁻¹, hneg] at hm
    exact hm
  have hqh : centerQuotientCartanMap H h = coroot (E α).val := by
    apply Subtype.ext
    exact centerQuotient_sl2_h_eq_coroot H χs.val χs.property hp.isSl2Triple he hf
      hp.bracket_mem
  have hact (t : H) : affineGroupAdjointRepresentation g (t : 𝔤) =
      (t : 𝔤) - characterDifferentialOnImage π hπ α.val t • (h : 𝔤) :=
    hp.adjoint_rootReflectionPoint hπ t
  have hαh : characterDifferentialOnImage π hπ α.val h = 2 :=
    hp.characterDifferential_bracket hπ
  intro β d hd
  let γ := E.symm (P.reflectionPerm (E α) (E β))
  have hAd (t : H) : affineGroupAdjointRepresentation g (t : 𝔤) ∈ H :=
    hp.adjoint_rootReflectionPoint_mem hπ t
  let R : H → H := fun t => ⟨affineGroupAdjointRepresentation g (t : 𝔤), hAd t⟩
  have hR (t : H) : R t = t - characterDifferentialOnImage π hπ α.val t • h := by
    apply Subtype.ext
    exact hact t
  have honto (t : H) : ∃ u : H,
      affineGroupAdjointRepresentation g (u : 𝔤) = (t : 𝔤) :=
    hp.adjoint_rootReflectionPoint_onto hπ t
  have hquotR (t : H) : centerQuotientCartanMap H (R t) =
      P.coreflection (E α) (centerQuotientCartanMap H t) := by
    rw [hR t, map_sub, map_smul, hqh, RootPairing.coreflection_apply,
      LieAlgebra.IsKilling.rootSystem_coroot_apply]
    congr 2
    rw [← ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB α t]
    rfl
  have hcoeff (t : H) : characterDifferentialOnImage π hπ γ.val (R t) =
      characterDifferentialOnImage π hπ β.val t := by
    rw [← ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB γ (R t),
      ← ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB β t]
    change (E γ).val (centerQuotientCartanMap H (R t)) =
      (E β).val (centerQuotientCartanMap H t)
    rw [show E γ = P.reflectionPerm (E α) (E β) from E.apply_symm_apply _, hquotR]
    exact RankOne.reflection_coreflection (centerQuotientCartan H)
      (E α) (E β) (centerQuotientCartanMap H t)
  have heigen (t : H) : ⁅(t : 𝔤), d⁆ =
      characterDifferentialOnImage π hπ β.val t • d :=
    RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ β.val d hd t
  have hroot := AffineGroupAdjoint.mem_rootSpace_of_eigen_transport H g
    (characterDifferentialOnImage π hπ β.val)
    (characterDifferentialOnImage π hπ γ.val) hAd honto hcoeff d heigen
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ γ.val]
  exact hroot

set_option maxHeartbeats 400000 in
/-- **Root-space transport.** The reflection point `n = x(1) y(-1) x(1)` of an
`sl₂`-normalized pair for `α` maps each entire occurring nonidentity `β`
character space *onto* the `s_α(β)` character space, where
`s_α(β) = E⁻¹ (reflectionPerm (E α) (E β))`. -/
theorem IsRootSl2Pair.rootReflectionPoint_characterSpace_map
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1})
    {x y : B →ₐc[K] SymmetricAlgebra K K} (hp : IsRootSl2Pair π α.val x y) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ∀ β : {β : M // affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
      (affineGroupCharacterWeightSpace π β.val).map
          ((affineGroupAdjointLieEquiv (rootReflectionPoint x y)).toLinearEquiv :
            𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π
          (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
            (E α) (E β))).val := by
  intro _ _ _ _ _ H E
  have hmem := hp.rootReflectionPoint_characterSpace_mem I hI π hπ hker hB α
  intro β
  let γ := E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm (E α) (E β))
  apply Submodule.eq_of_le_of_finrank_eq
  · intro d hd
    obtain ⟨z, hz, rfl⟩ := hd
    exact hmem β z hz
  · rw [((affineGroupAdjointLieEquiv (rootReflectionPoint x y)).toLinearEquiv).finrank_map_eq]
    exact (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB
      β.val β.property.2 β.property.1).trans
      (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB
        γ.val γ.property.2 γ.property.1).symm

set_option maxHeartbeats 400000 in
/-- **Root-subgroup conjugation.** For the reflection point `n` of an
`sl₂`-normalized pair for `α`, every occurring nonidentity `β` and every
`Ga` morphism `z` with tangent in the `β` character space, there is a
`Ga` morphism `z'` with tangent `Ad(n)(dz)`, lying in the `s_α(β)` character
space, such that `n z(u) n⁻¹ = z'(u)` for every `u ∈ K`. -/
theorem IsRootSl2Pair.rootReflectionPoint_ga_conjugation
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1})
    {x y : B →ₐc[K] SymmetricAlgebra K K} (hp : IsRootSl2Pair π α.val x y) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    ∀ β : {β : M // affineGroupCharacterWeightSpace π β ≠ ⊥ ∧ β ≠ 1},
      ∀ z : B →ₐc[K] SymmetricAlgebra K K,
        gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π β.val →
        ∃ z' : B →ₐc[K] SymmetricAlgebra K K,
          gaAffineGroupTangent z' =
            affineGroupAdjointRepresentation (rootReflectionPoint x y)
              (gaAffineGroupTangent z) ∧
          gaAffineGroupTangent z' ∈ affineGroupCharacterWeightSpace π
            (E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm
              (E α) (E β))).val ∧
          ∀ u : K,
            rootReflectionPoint x y * gaAffineGroupPoints z (Multiplicative.ofAdd u) *
                (rootReflectionPoint x y)⁻¹ =
              gaAffineGroupPoints z' (Multiplicative.ofAdd u) := by
  intro _ _ _ _ _ H E
  have hmem := hp.rootReflectionPoint_characterSpace_mem I hI π hπ hker hB α
  intro β z hz
  let γ := E.symm ((rootSystem (centerQuotientCartan H)).reflectionPerm (E α) (E β))
  have hd' : affineGroupAdjointRepresentation (rootReflectionPoint x y)
      (gaAffineGroupTangent z) ∈ affineGroupCharacterWeightSpace π γ.val := hmem β _ hz
  obtain ⟨z', hz', _⟩ :=
    CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ γ.val γ.property.2 _ hd'
  refine ⟨z', hz', hz' ▸ hd', ?_⟩
  intro u
  have htan : affineGroupAdjointRepresentation (rootReflectionPoint x y)
      (gaAffineGroupTangent z) = (1 : K) • gaAffineGroupTangent z' := by
    rw [hz', one_smul]
  simpa only [one_mul] using
    GaAffineGroupPoints.conjugate_of_tangent_eq z z' (rootReflectionPoint x y) 1 htan u

end ReductiveGroups
