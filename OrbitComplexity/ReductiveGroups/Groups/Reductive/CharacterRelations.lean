import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialInjective


/-! # Integral roots and torus characters

Differentiating characters identifies their integral relations with the integral relations
among roots of the center quotient. The simple-root assignment therefore embeds the root
lattice into the character lattice and preserves the ranks of selected root spans.

## Main definitions

* `rootCharacterMap`: the integral root-lattice map into the torus character lattice.

## Main results

* `rootCharacter_relation`: integral root relations are multiplicative character relations.
* `rootCharacterMap_root`: the root-lattice map sends each root to its character.
* `rootCharacterMap_injective`: the root-lattice map is injective.
* `rootCharacter_span_rank`: selected roots and their characters have equal integral span rank.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti LieAlgebra
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def differentialHom : G.characters →*
    Multiplicative (Module.Dual K G.torusTangent) where
  toFun χ := Multiplicative.ofAdd
    (characterDifferentialOnImage G.torusSplit G.split_surjective χ)
  map_one' := by
    change characterDifferentialOnImage G.torusSplit G.split_surjective 1 = 0
    ext t
    simp [characterDifferentialOnImage]
  map_mul' χ ψ := by
    change characterDifferentialOnImage G.torusSplit G.split_surjective (χ * ψ) =
      characterDifferentialOnImage G.torusSplit G.split_surjective χ +
        characterDifferentialOnImage G.torusSplit G.split_surjective ψ
    ext t
    simp [characterDifferentialOnImage, characterDifferential_mul]

private theorem root_differential (r : G.rootIndex) (t : G.torusTangent) :
    G.rootSystem.root r (centerQuotientCartanMap G.torusTangent t) =
      characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) t := by
  have h := ReductiveCharacterCenterQuotientRootEquiv.apply_map
    G.torusIdeal G.isMaximalTorus G.torusSplit G.split_surjective G.split_eq_zero
    G.reductive (G.characterRootEquiv.symm r) t
  change G.rootSystem.root (G.characterRootEquiv (G.characterRootEquiv.symm r))
    (centerQuotientCartanMap G.torusTangent t) = _ at h
  simpa only [rootCharacter, Equiv.apply_symm_apply] using h

private theorem differential_prod (m : G.rootIndex →₀ ℤ) :
    characterDifferentialOnImage G.torusSplit G.split_surjective
      (m.prod fun r e => G.rootCharacter r ^ e) =
        m.sum fun r e => e •
          characterDifferentialOnImage G.torusSplit G.split_surjective (G.rootCharacter r) := by
  have h := map_prod (differentialHom G) (fun r => G.rootCharacter r ^ m r) m.support
  simp only [map_zpow] at h
  exact congrArg Multiplicative.toAdd h

/-- Integral relations among roots agree with multiplicative relations among their characters. -/
theorem rootCharacter_relation (m : G.rootIndex →₀ ℤ) :
    (m.prod fun r e => G.rootCharacter r ^ e) = 1 ↔
      (m.sum fun r e => e • G.rootSystem.root r) = 0 := by
  constructor
  · intro h
    ext t
    obtain ⟨s, rfl⟩ := centerQuotientCartanMap_surjective G.torusTangent t
    have hd := differential_prod G m
    rw [h] at hd
    have hz : characterDifferentialOnImage G.torusSplit G.split_surjective 1 = 0 := by
      ext s
      simp [characterDifferentialOnImage]
    rw [hz] at hd
    have he := LinearMap.congr_fun hd s
    simpa only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, root_differential] using he.symm
  · intro h
    apply characterDifferentialOnImage_injective G.torusSplit G.split_surjective
    dsimp only
    rw [differential_prod]
    ext t
    have he := LinearMap.congr_fun h (centerQuotientCartanMap G.torusTangent t)
    simpa only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, root_differential, characterDifferentialOnImage,
      LinearMap.comp_apply, characterDifferential_one] using he

private def differentialLinear : (G.torusIndex →₀ ℤ) →ₗ[ℤ]
    Module.Dual K G.torusTangent :=
  (differentialHom G).toAdditive.toIntLinearMap

/-- Simple-root characters are independent in the integral character lattice. -/
theorem rootCharacter_independent :
    LinearIndependent ℤ (fun i : G.rootBase.support => (G.rootCharacter i).toAdd) := by
  let q : G.torusTangent →ₗ[K] G.cartan :=
    (centerQuotientCartanMap G.torusTangent).toLinearMap
  have hq : Function.Injective q.dualMap := by
    intro f g h
    ext t
    obtain ⟨s, rfl⟩ := centerQuotientCartanMap_surjective G.torusTangent t
    exact LinearMap.congr_fun h s
  have hb : LinearIndependent K (fun i : G.rootBase.support => G.rootSystem.root i) :=
    G.rootBase.linearIndepOn_root
  have hd := (hb.map' q.dualMap (LinearMap.ker_eq_bot.mpr hq)).restrict_scalars' ℤ
  apply LinearIndependent.of_comp (differentialLinear G)
  convert hd using 1
  funext i
  ext t
  exact (root_differential G i t).symm

/-- The simple-root character assignment extends linearly to the integral root lattice. -/
def rootCharacterMap : G.rootSystem.rootSpan ℤ →ₗ[ℤ] (G.torusIndex →₀ ℤ) :=
  G.rootBase.toWeightBasisInt.constr ℤ
    (fun i : G.rootBase.support => (G.rootCharacter i).toAdd)

private theorem map_differential (x : G.rootSystem.rootSpan ℤ) (t : G.torusTangent) :
    differentialLinear G (rootCharacterMap G x) t =
      x.val (centerQuotientCartanMap G.torusTangent t) := by
  let q : G.torusTangent →ₗ[K] G.cartan :=
    (centerQuotientCartanMap G.torusTangent).toLinearMap
  let f : G.rootSystem.rootSpan ℤ →ₗ[ℤ] Module.Dual K G.torusTangent :=
    (q.dualMap.restrictScalars ℤ).comp (G.rootSystem.rootSpan ℤ).subtype
  have h : (differentialLinear G).comp (rootCharacterMap G) = f := by
    apply G.rootBase.toWeightBasisInt.ext
    intro i
    rw [LinearMap.comp_apply]
    have hb : rootCharacterMap G (G.rootBase.toWeightBasisInt i) =
        (G.rootCharacter i).toAdd :=
      G.rootBase.toWeightBasisInt.constr_basis ℤ _ i
    rw [hb]
    ext t
    change characterDifferentialOnImage G.torusSplit G.split_surjective
      (G.rootCharacter i) t =
        (G.rootBase.toWeightBasisInt i).val (centerQuotientCartanMap G.torusTangent t)
    rw [RootPairing.Base.coe_toWeightBasisInt_apply]
    exact (root_differential G i t).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) t

/-- The root-lattice map sends each root to its corresponding torus character. -/
theorem rootCharacterMap_root (r : G.rootIndex) :
    rootCharacterMap G (G.rootSystem.rootSpanMem ℤ r) = (G.rootCharacter r).toAdd := by
  have h := characterDifferentialOnImage_injective G.torusSplit G.split_surjective
  apply Multiplicative.ofAdd.injective
  apply h
  ext t
  change differentialLinear G (rootCharacterMap G (G.rootSystem.rootSpanMem ℤ r)) t = _
  rw [map_differential]
  exact root_differential G r t

/-- The integral root lattice embeds into the torus character lattice. -/
theorem rootCharacterMap_injective : Function.Injective (rootCharacterMap G) := by
  intro x y h
  apply Subtype.ext
  ext t
  obtain ⟨s, rfl⟩ := centerQuotientCartanMap_surjective G.torusTangent t
  rw [← map_differential, ← map_differential, h]

/-- The integral span of selected roots maps onto the span of their characters. -/
theorem rootCharacterMap_span (roots : Set G.rootIndex) :
    (Submodule.span ℤ (G.rootSystem.rootSpanMem ℤ '' roots)).map (rootCharacterMap G) =
      Submodule.span ℤ ((fun r => (G.rootCharacter r).toAdd) '' roots) := by
  rw [Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro r _
  exact rootCharacterMap_root G r

/-- Selected roots and their torus characters have the same integral span rank. -/
theorem rootCharacter_span_rank (roots : Set G.rootIndex) :
    Module.finrank ℤ (Submodule.span ℤ ((fun r => (G.rootCharacter r).toAdd) '' roots)) =
      Module.finrank ℤ (Submodule.span ℤ (G.rootSystem.rootSpanMem ℤ '' roots)) := by
  rw [← rootCharacterMap_span]
  exact congrArg Cardinal.toNat (rank_map_eq (rootCharacterMap_injective G) _)

end ReductiveGroups.ReductiveGroupData
