import OrbitComplexity.ReductiveGroups.Roots.OrderSix
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCorootSquare
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupReflectionSquare
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPinnedParameters
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupCommutation
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Six-term braid relations for the chosen simple representatives -/

namespace ReductiveGroups.OrderSix

/-- A fourth-power and square-conjugation relation turn commuting conjugates into a braid. -/
private theorem braid_of_conjugate_commute {H : Type*} [Group H] (a b : H)
    (hfour : b ^ 4 = 1)
    (hconj : b ^ 2 * a * (b ^ 2)⁻¹ = a⁻¹)
    (hcomm : Commute b ((a * b) * a * (a * b)⁻¹)) :
    a * b * a * b * a * b = b * a * b * a * b * a := by
  have hbinv : b⁻¹ = b * b ^ 2 := by
    calc
      b⁻¹ = b⁻¹ * b ^ 4 := by rw [hfour]; simp
      _ = b * b ^ 2 := by group
  have hka : b ^ 2 * a⁻¹ = a * b ^ 2 := by
    calc
      b ^ 2 * a⁻¹ = (b ^ 2 * a * (b ^ 2)⁻¹)⁻¹ * b ^ 2 := by group
      _ = a * b ^ 2 := by rw [hconj, inv_inv]
  have hr : (a * b) * a * (a * b)⁻¹ = a * b * a * b * a * b ^ 2 := by
    calc
      _ = a * b * a * b⁻¹ * a⁻¹ := by group
      _ = a * b * a * b * (b ^ 2 * a⁻¹) := by rw [hbinv]; group
      _ = _ := by rw [hka]; group
  apply mul_right_cancel (b := b ^ 2)
  calc
    (a * b * a * b * a * b) * b ^ 2 =
        ((a * b) * a * (a * b)⁻¹) * b := by rw [hr]; group
    _ = b * ((a * b) * a * (a * b)⁻¹) := hcomm.eq.symm
    _ = (b * a * b * a * b * a) * b ^ 2 := by rw [hr]; group

end ReductiveGroups.OrderSix

noncomputable section
namespace ReductiveGroups.OrderSix
open TauCeti WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem representative_four (j : G.rootBase.support) :
    (G.reflectionPoint j.val) ^ 4 = 1 := by
  let z : WithConv (MonoidAlgebra K (Multiplicative ℤ) →ₐ[K] K) :=
    (DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ (-1))
  have hz : z * z = 1 := by
    apply (DiagonalizableGroup.pointsMulEquiv (R := K) (A := K)
      (G := Multiplicative ℤ)).injective
    rw [map_mul, map_one]
    simp only [z, MulEquiv.apply_symm_apply]
    apply MonoidHom.ext
    intro m
    change ((-1 : Kˣ) ^ m.toAdd) * ((-1 : Kˣ) ^ m.toAdd) = 1
    rw [← mul_zpow]
    simp
  calc
    (G.reflectionPoint j.val) ^ 4 =
        (G.reflectionPoint j.val) ^ 2 * (G.reflectionPoint j.val) ^ 2 := by group
    _ = Coroot.simpleCorootPoint G j (-1) * Coroot.simpleCorootPoint G j (-1) := by
      rw [Coroot.simple_square_eq_coroot]
    _ = (AlgHom.mapDomain (Coroot.simpleCorootMap G j)) z *
        (AlgHom.mapDomain (Coroot.simpleCorootMap G j)) z := by
      rw [Coroot.simpleCorootPoint_map]
    _ = 1 := by rw [← map_mul, hz, map_one]

private theorem negative_pairing (i j : G.rootIndex) :
    G.rootSystem.pairingIn ℤ (-i) j = -G.rootSystem.pairingIn ℤ i j := by
  have hr : G.rootSystem.root (-i) = -G.rootSystem.root i := by simp
  have hc : G.rootSystem.pairing (-i) j = -G.rootSystem.pairing i j := by
    rw [← G.rootSystem.root_coroot_eq_pairing,
      ← G.rootSystem.root_coroot_eq_pairing, hr, map_neg, LinearMap.neg_apply]
  rw [← G.rootSystem.algebraMap_pairingIn ℤ (-i) j,
    ← G.rootSystem.algebraMap_pairingIn ℤ i j] at hc
  exact_mod_cast hc

private theorem square_conjugate_ga (j : G.rootBase.support) (r : G.rootIndex)
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r)
    (hp : G.rootSystem.pairingIn ℤ r j.val = -1 ∨
      G.rootSystem.pairingIn ℤ r j.val = -3 ∨
      G.rootSystem.pairingIn ℤ r j.val = 1 ∨
      G.rootSystem.pairingIn ℤ r j.val = 3) (t : K) :
    (G.reflectionPoint j.val) ^ 2 * gaParameterPoint x t *
      ((G.reflectionPoint j.val) ^ 2)⁻¹ = gaParameterPoint x (-t) := by
  have hw := G.simpleReflection_square_weight j r (gaAffineGroupTangent x) hx
  have he : (-1 : K) ^ G.rootSystem.pairingIn ℤ r j.val = -1 := by
    rcases hp with hp | hp | hp | hp <;> rw [hp] <;> norm_num
  rw [he] at hw
  simpa only [gaParameterPoint, gaAffineGroupPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, neg_one_mul] using
    GaAffineGroupPoints.conjugate_of_tangent_eq x x _ (-1) hw t

private theorem square_conjugate_simple (i j : G.rootBase.support)
    (hp : G.rootSystem.pairingIn ℤ i.val j.val = -1 ∨
      G.rootSystem.pairingIn ℤ i.val j.val = -3) :
    (G.reflectionPoint j.val) ^ 2 * G.reflectionPoint i.val *
      ((G.reflectionPoint j.val) ^ 2)⁻¹ = (G.reflectionPoint i.val)⁻¹ := by
  have hpos := square_conjugate_ga G j i.val (G.simpleRootMap i)
    (G.simpleRootMap_tangent_mem i) (hp.elim Or.inl (Or.inr ∘ Or.inl))
  have hneg : G.rootSystem.pairingIn ℤ (-i.val) j.val = 1 ∨
      G.rootSystem.pairingIn ℤ (-i.val) j.val = 3 := by
    rw [negative_pairing]
    rcases hp with hp | hp <;> simp [hp]
  have hneg := square_conjugate_ga G j (-i.val) (G.negativeSimpleRootMap i)
    (G.negativeRootMap_tangent_mem i)
    (hneg.elim (Or.inr ∘ Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr))
  have hi : G.reflectionPoint i.val =
      gaParameterPoint (G.simpleRootMap i) 1 *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1) *
          gaParameterPoint (G.simpleRootMap i) 1 := rfl
  rw [hi]
  calc
    _ = ((G.reflectionPoint j.val) ^ 2 * gaParameterPoint (G.simpleRootMap i) 1 *
          ((G.reflectionPoint j.val) ^ 2)⁻¹) *
        ((G.reflectionPoint j.val) ^ 2 * gaParameterPoint (G.negativeSimpleRootMap i) (-1) *
          ((G.reflectionPoint j.val) ^ 2)⁻¹) *
        ((G.reflectionPoint j.val) ^ 2 * gaParameterPoint (G.simpleRootMap i) 1 *
          ((G.reflectionPoint j.val) ^ 2)⁻¹) := by group
    _ = gaParameterPoint (G.simpleRootMap i) (-1) *
        gaParameterPoint (G.negativeSimpleRootMap i) 1 *
          gaParameterPoint (G.simpleRootMap i) (-1) := by
      rw [hpos, hneg]
      simp only [neg_neg]
    _ = _ := by
      simp only [gaParameterPoint, ofAdd_neg, map_inv, mul_inv_rev, inv_inv]
      group

/-- Odd Cartan entries give the fourth-power and square-conjugation relations. -/
private theorem square_facts (i j : G.rootBase.support)
    (hp : G.rootSystem.pairingIn ℤ i.val j.val = -1 ∨
      G.rootSystem.pairingIn ℤ i.val j.val = -3) :
    (G.reflectionPoint j.val) ^ 4 = 1 ∧
    (G.reflectionPoint j.val) ^ 2 * G.reflectionPoint i.val *
      ((G.reflectionPoint j.val) ^ 2)⁻¹ = (G.reflectionPoint i.val)⁻¹ :=
  ⟨representative_four G j, square_conjugate_simple G i j hp⟩

end ReductiveGroups.OrderSix

noncomputable section
namespace ReductiveGroups.OrderSix
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem root_eq_sum_of_character (r s t : G.rootIndex)
    (h : G.rootCharacter t = G.rootCharacter r * G.rootCharacter s) :
    G.rootSystem.root t = G.rootSystem.root r + G.rootSystem.root s := by
  have hm : G.rootCharacterMap
      (G.rootSystem.rootSpanMem ℤ r + G.rootSystem.rootSpanMem ℤ s) =
        (G.rootCharacter r).toAdd + (G.rootCharacter s).toAdd :=
    (map_add G.rootCharacterMap _ _).trans
      (congrArg₂ (fun a b => a + b)
        (G.rootCharacterMap_root r) (G.rootCharacterMap_root s))
  have ht : G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ t) =
      G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ r +
        G.rootSystem.rootSpanMem ℤ s) :=
    (G.rootCharacterMap_root t).trans ((congrArg Multiplicative.toAdd h).trans hm.symm)
  exact congrArg Subtype.val (G.rootCharacterMap_injective ht)

private theorem root_bracket_zero (r s : G.rootIndex)
    (hne : G.rootSystem.root r + G.rootSystem.root s ≠ 0)
    (hnot : G.rootSystem.root r + G.rootSystem.root s ∉ Set.range G.rootSystem.root)
    (d e : G.tangent) (hd : d ∈ G.rootWeightSpace r) (he : e ∈ G.rootWeightSpace s) :
    ⁅d, e⁆ = 0 := by
  have hchar : G.rootCharacter r * G.rootCharacter s ≠ 1 := by
    intro h
    have hm : G.rootCharacterMap
        (G.rootSystem.rootSpanMem ℤ r + G.rootSystem.rootSpanMem ℤ s) =
          G.rootCharacterMap 0 := by
      rw [map_add, G.rootCharacterMap_root r, G.rootCharacterMap_root s, map_zero]
      exact congrArg Multiplicative.toAdd h
    exact hne (congrArg Subtype.val (G.rootCharacterMap_injective hm))
  by_contra hz
  have hb := lie_mem_affineGroupCharacterWeightSpace G.torusSplit
    (G.rootCharacter r) (G.rootCharacter s) d e hd he
  have hspace : affineGroupCharacterWeightSpace G.torusSplit
      (G.rootCharacter r * G.rootCharacter s) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨⁅d, e⁆, hb, hz⟩
  let chi : {a : G.characters //
      affineGroupCharacterWeightSpace G.torusSplit a ≠ ⊥ ∧ a ≠ 1} :=
    ⟨G.rootCharacter r * G.rootCharacter s, hspace, hchar⟩
  let t := G.characterRootEquiv chi
  have ht : G.rootCharacter t = G.rootCharacter r * G.rootCharacter s :=
    congrArg Subtype.val (G.characterRootEquiv.symm_apply_apply chi)
  exact hnot ⟨t, root_eq_sum_of_character G r s t ht⟩

private theorem commute_ga (j : G.rootBase.support) (r : G.rootIndex)
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r)
    (hp : G.rootSystem.root j.val + G.rootSystem.root r ≠ 0 ∧
      G.rootSystem.root j.val + G.rootSystem.root r ∉ Set.range G.rootSystem.root)
    (hn : -G.rootSystem.root j.val + G.rootSystem.root r ≠ 0 ∧
      -G.rootSystem.root j.val + G.rootSystem.root r ∉ Set.range G.rootSystem.root)
    (t : K) : Commute (G.reflectionPoint j.val) (gaParameterPoint x t) := by
  have hpos := root_bracket_zero G j.val r hp.1 hp.2
    _ _ (G.simpleRootMap_tangent_mem j) hx
  have hneg := root_bracket_zero G (-j.val) r
    (by simpa using hn.1) (by simpa using hn.2)
    _ _ (G.negativeRootMap_tangent_mem j) hx
  have hc := GaAffineGroupPoints.commute_of_tangent_bracket_zero
    (G.simpleRootMap j) x hpos 1 t
  have hd := GaAffineGroupPoints.commute_of_tangent_bracket_zero
    (G.negativeSimpleRootMap j) x hneg (-1) t
  change Commute
    (gaParameterPoint (G.simpleRootMap j) 1 *
      gaParameterPoint (G.negativeSimpleRootMap j) (-1) *
        gaParameterPoint (G.simpleRootMap j) 1) (gaParameterPoint x t)
  simpa only [gaAffineGroupPoints, MonoidHom.comp_apply, gaParameterPoint,
    MulEquiv.coe_toMonoidHom] using
    (hc.mul_left hd).mul_left hc

/-- In the order-six case, the second representative commutes with the indicated conjugate. -/
private theorem commute_conjugate (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 6) :
    Commute (G.reflectionPoint j.val)
      ((G.reflectionPoint i.val * G.reflectionPoint j.val) *
        G.reflectionPoint i.val *
          (G.reflectionPoint i.val * G.reflectionPoint j.val)⁻¹) := by
  obtain ⟨_, _, φ, _, hφ, hsimple, _, _, hword⟩ := G.exists_rootParameterFamily
  let g (r : G.rootIndex) := G.rootSystem.reflectionPerm i.val
    (G.rootSystem.reflectionPerm j.val r)
  let p := G.reflectionPoint i.val * G.reflectionPoint j.val
  have hforward (r : G.rootIndex) :
      ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
        p * gaParameterPoint (φ r) t * p⁻¹ = gaParameterPoint (φ (g r)) (ε * t) := by
    obtain ⟨ε, hε, he⟩ := hword [j, i] (g r)
    have hw : G.rootSystem.weylGroupToPerm
        (simpleWeylWord G.rootBase [j, i]) (g r) = r := by
      simp only [simpleWeylWord, map_mul, weylGroupToPerm_simple,
        Equiv.Perm.mul_apply]
      simp only [map_one, Equiv.Perm.one_apply, g, G.rootSystem.reflectionPerm_self]
    have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
    have hh (t : K) : p⁻¹ * gaParameterPoint (φ (g r)) (ε * t) * p =
        gaParameterPoint (φ r) t := by
      have h' := he (ε * t)
      rw [hw, ← mul_assoc, hεsq, one_mul] at h'
      simpa only [p, simpleWordPoint_cons, simpleWordPoint_nil, mul_one,
        mul_inv_rev, inv_inv] using h'
    refine ⟨ε, hε, fun t => ?_⟩
    calc
      _ = p * (p⁻¹ * gaParameterPoint (φ (g r)) (ε * t) * p) * p⁻¹ := by rw [hh]
      _ = _ := by group
  have hs := (order_six_simple_sums G.rootSystem G.rootBase i j h).2
  dsimp only at hs
  have hgm : G.rootSystem.root (g (-i.val)) = -G.rootSystem.root (g i.val) := by
    have hn : G.rootSystem.root (-i.val) = -G.rootSystem.root i.val := by simp
    simp only [g, G.rootSystem.root_reflectionPerm, hn, map_neg]
  have hc (t : K) : Commute (G.reflectionPoint j.val) (gaParameterPoint (φ (g i.val)) t) :=
    commute_ga G j (g i.val) (φ (g i.val)) (hφ _).1 hs.1 hs.2.2.1 t
  have hd (t : K) : Commute (G.reflectionPoint j.val) (gaParameterPoint (φ (g (-i.val))) t) :=
    commute_ga G j (g (-i.val)) (φ (g (-i.val))) (hφ _).1
      (by simpa only [hgm, sub_eq_add_neg] using hs.2.1)
      (by simpa only [hgm, sub_eq_add_neg] using hs.2.2.2) t
  obtain ⟨ε, _, he⟩ := hforward i.val
  obtain ⟨δ, _, hd'⟩ := hforward (-i.val)
  have hi : G.reflectionPoint i.val =
      gaParameterPoint (φ i.val) 1 * gaParameterPoint (φ (-i.val)) (-1) *
        gaParameterPoint (φ i.val) 1 := by rw [(hsimple i).1, (hsimple i).2]; rfl
  have hr : p * G.reflectionPoint i.val * p⁻¹ =
      gaParameterPoint (φ (g i.val)) (ε * 1) *
        gaParameterPoint (φ (g (-i.val))) (δ * (-1)) *
          gaParameterPoint (φ (g i.val)) (ε * 1) := by
    calc
      _ = p * (gaParameterPoint (φ i.val) 1 * gaParameterPoint (φ (-i.val)) (-1) *
          gaParameterPoint (φ i.val) 1) * p⁻¹ := congrArg (fun z => p * z * p⁻¹) hi
      _ = (p * gaParameterPoint (φ i.val) 1 * p⁻¹) *
          (p * gaParameterPoint (φ (-i.val)) (-1) * p⁻¹) *
          (p * gaParameterPoint (φ i.val) 1 * p⁻¹) := by group
      _ = _ := by rw [he, hd']
  change Commute (G.reflectionPoint j.val) (p * G.reflectionPoint i.val * p⁻¹)
  rw [hr]
  exact ((hc _).mul_right (hd _)).mul_right (hc _)

end ReductiveGroups.OrderSix

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Chosen simple representatives satisfy the six-term braid at Coxeter order six. -/
theorem reflectionPoints_braid_six (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 6) :
    G.reflectionPoint i.val * G.reflectionPoint j.val *
      G.reflectionPoint i.val * G.reflectionPoint j.val *
        G.reflectionPoint i.val * G.reflectionPoint j.val =
    G.reflectionPoint j.val * G.reflectionPoint i.val *
      G.reflectionPoint j.val * G.reflectionPoint i.val *
        G.reflectionPoint j.val * G.reflectionPoint i.val := by
  have hc := (OrderSix.order_six_simple_sums G.rootSystem G.rootBase i j h).1
  have hp : G.rootSystem.pairingIn ℤ i.val j.val = -1 ∨
      G.rootSystem.pairingIn ℤ i.val j.val = -3 := hc.elim
    (fun hc => Or.inl hc.1) (fun hc => Or.inr hc.1)
  obtain ⟨hfour, hconj⟩ := OrderSix.square_facts G i j hp
  exact OrderSix.braid_of_conjugate_commute _ _ hfour hconj
    (OrderSix.commute_conjugate G i j h)

end ReductiveGroups.ReductiveGroupData
