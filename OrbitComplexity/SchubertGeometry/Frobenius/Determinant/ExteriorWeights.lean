import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Torus
import OrbitComplexity.ReductiveGroups.Roots.Characters.CharacterHeight
import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterWeightDecomposition
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootSums
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Fintype.EquivFin
import TauCeti.RingTheory.FiniteType.PointSeparation
import OrbitComplexity.FrobeniusSplitting.Normality.Models.PositiveSum

/-! # Weight coordinates for the degree-dim Lie(U) adjoint exterior representation -/

open ReductiveGroups TauCeti GroupActions
open scoped BigOperators TensorProduct
noncomputable section
universe u

namespace SchubertGeometry.DeterminantWeights

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The basis consists of N-fold wedges of a full torus weight basis of Lie(G). -/
def determinantExteriorBasis :
    Module.Basis
      (Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
        (Module.finrank K G.unipotentTangent)) K
      (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent) :=
  (adjointWeightBasis G.torusSplit).exteriorPower (Module.finrank K G.unipotentTangent)

/-- A wedge weight is the product of its full torus characters, including identity weights. -/
def determinantExteriorCharacter
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    G.characters :=
  ∏ i ∈ s.val, adjointWeightCharacter G.torusSplit i

/-- The exterior adjoint action is diagonal in these degree-N coordinates. -/
theorem determinantExteriorBasis_torus
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    exteriorPower.map (Module.finrank K G.unipotentTangent)
        (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z))
        (determinantExteriorBasis G s) =
      z.ofConv (MonoidAlgebra.single (determinantExteriorCharacter G s) (1 : K)) •
        determinantExteriorBasis G s := by
  have h := exteriorPower.map_basis_exteriorPower_of_apply_basis
    (adjointWeightBasis G.torusSplit)
    (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z))
    (fun i => z.ofConv (MonoidAlgebra.single (adjointWeightCharacter G.torusSplit i) (1 : K)))
    (adjointWeightBasis_torus G.torusSplit z) (Module.finrank K G.unipotentTangent) s
  have hp : (∏ i ∈ s.val,
      z.ofConv (MonoidAlgebra.single (adjointWeightCharacter G.torusSplit i) (1 : K))) =
      z.ofConv (MonoidAlgebra.single (determinantExteriorCharacter G s) (1 : K)) := by
    rw [← map_prod, MonoidAlgebra.prod_single]
    simp only [determinantExteriorCharacter, Finset.prod_const_one]
  exact h.trans (congrArg (fun a : K => a • determinantExteriorBasis G s) hp)

/-- The same full-character formula holds for the constructed algebraic exterior comodule. -/
theorem determinantExteriorBasis_points
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    let := DeterminantSection.adjointExteriorComodule G
    Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _
        (AlgHom.mapDomain G.torusSplit z) (determinantExteriorBasis G s) =
      z.ofConv (MonoidAlgebra.single (determinantExteriorCharacter G s) (1 : K)) •
        determinantExteriorBasis G s := by
  let := DeterminantSection.adjointExteriorComodule G
  exact (DeterminantSection.adjointExterior_points G
    (AlgHom.mapDomain G.torusSplit z) (determinantExteriorBasis G s)).trans
      (determinantExteriorBasis_torus G z s)

private theorem determinantExteriorBasis_coact
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    let := DeterminantSection.adjointExteriorComodule G
    TensorProduct.map LinearMap.id G.torusSplit.toCoalgHom.toLinearMap
        (Comodule.coact (R := K) (C := G.coordinateAlgebra)
          (determinantExteriorBasis G s)) =
      determinantExteriorBasis G s ⊗ₜ[K]
        MonoidAlgebra.single (determinantExteriorCharacter G s) (1 : K) := by
  let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  let := DeterminantSection.adjointExteriorComodule G
  have hb := adjointWeightBasis_weightSpace G.torusSplit
  have h := @exteriorBasis_weightSpace.{u,u,u,u} K G.coordinateAlgebra G.tangent G.characters
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)) inferInstance
    (adjointWeightRank G.torusSplit) G.torusSplit (adjointWeightBasis G.torusSplit)
    (adjointWeightCharacter G.torusSplit) hb (Module.finrank K G.unipotentTangent) s
  exact DiagonalizableGroup.mem_weightSpace.mp h

/-- The diagonal wedge formula is an identity of the constructed coaction. -/
theorem determinantExteriorBasis_mem_weight
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    let := DeterminantSection.adjointExteriorComodule G
    determinantExteriorBasis G s ∈
      DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom (determinantExteriorCharacter G s) := by
  let := DeterminantSection.adjointExteriorComodule G
  exact DiagonalizableGroup.mem_weightSpace.mpr (determinantExteriorBasis_coact G s)

private theorem exterior_coordinate_vanishes (chi : G.characters)
    (v : ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent))
    (hs : determinantExteriorCharacter G s ≠ chi) :
    let := DeterminantSection.adjointExteriorComodule G
    v ∈ DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom chi →
      (determinantExteriorBasis G).repr v s = 0 := by
  classical
  let := DeterminantSection.adjointExteriorComodule G
  dsimp only
  intro hv
  let E := ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent
  let b := determinantExteriorBasis G
  let q := G.torusSplit.toCoalgHom.toLinearMap
  let lid : K ⊗[K] MonoidAlgebra K G.characters →ₗ[K] MonoidAlgebra K G.characters :=
    (TensorProduct.lid K (MonoidAlgebra K G.characters)).toLinearMap
  have hlid (a : K) (z : MonoidAlgebra K G.characters) : lid (a ⊗ₜ[K] z) = a • z := rfl
  let L : E →ₗ[K] MonoidAlgebra K G.characters :=
    lid ∘ₗ TensorProduct.map (b.coord s) q ∘ₗ
        Comodule.coact (R := K) (C := G.coordinateAlgebra)
  have hL : L = (b.coord s).smulRight
      (MonoidAlgebra.single (determinantExteriorCharacter G s) (1 : K)) := by
    apply b.ext
    intro t
    have ht := congrArg
      (fun z => lid (TensorProduct.map (b.coord s) LinearMap.id z))
      (determinantExteriorBasis_coact G t)
    by_cases hts : t = s
    · subst t
      simpa only [L, LinearMap.comp_apply, TensorProduct.map_map,
        LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_tmul,
        LinearMap.id_apply, hlid, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_same, one_smul,
        LinearMap.smulRight_apply, b, q] using ht
    · simpa only [L, LinearMap.comp_apply, TensorProduct.map_map,
        LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_tmul,
        LinearMap.id_apply, hlid, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_of_ne' hts, zero_smul,
        LinearMap.smulRight_apply, b, q] using ht
  have hc : (b.repr v s) •
      MonoidAlgebra.single (determinantExteriorCharacter G s) (1 : K) =
      (b.repr v s) • MonoidAlgebra.single chi (1 : K) := by
    calc
      _ = L v := (LinearMap.congr_fun hL v).symm
      _ = _ := by
        have he := congrArg
          (fun z => lid (TensorProduct.map (b.coord s) LinearMap.id z))
          (DiagonalizableGroup.mem_weightSpace.mp hv)
        simpa only [L, LinearMap.comp_apply, TensorProduct.map_map,
          LinearMap.comp_id, LinearMap.id_comp, TensorProduct.map_tmul,
          LinearMap.id_apply, hlid, Module.Basis.coord_apply, q] using he
  have he := congrArg (fun z : MonoidAlgebra K G.characters =>
    z.coeff (determinantExteriorCharacter G s)) hc
  simpa only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hs, smul_eq_mul, mul_one, mul_zero] using he

private def coordinateWeightEquiv (chi : G.characters) :
    Derivation.adjointWeightSpace G.torusSplit chi ≃ₗ[K]
      affineGroupCharacterWeightSpace G.torusSplit chi :=
  (Derivation.cotangentLinearEquiv (R := K) (A := G.coordinateAlgebra) (B := K)).ofSubmodules _ _
    (Submodule.map_equiv_eq_comap_symm
      (Derivation.cotangentLinearEquiv (R := K) (A := G.coordinateAlgebra) (B := K))
      (Derivation.adjointWeightSpace G.torusSplit chi))

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateWeight_ne_bot (a : adjointWeightIndex G.torusSplit) :
    affineGroupCharacterWeightSpace G.torusSplit a.1 ≠ ⊥ := by
  intro hz
  have he := (coordinateWeightEquiv G a.1).finrank_eq
  rw [hz, finrank_bot] at he
  have ha := a.2.isLt
  omega

private def rawWeightRoot (a : adjointWeightIndex G.torusSplit) (ha : a.1 ≠ 1) : G.rootIndex :=
  G.characterRootEquiv ⟨a.1, coordinateWeight_ne_bot G a, ha⟩

private theorem rawWeightRoot_character (a : adjointWeightIndex G.torusSplit) (ha : a.1 ≠ 1) :
    G.rootCharacter (rawWeightRoot G a ha) = a.1 := by
  exact congrArg Subtype.val (G.characterRootEquiv.symm_apply_apply
    ⟨a.1, coordinateWeight_ne_bot G a, ha⟩)

private theorem coordinateRoot_finrank (r : G.rootIndex) :
    Module.finrank K (Derivation.adjointWeightSpace G.torusSplit (G.rootCharacter r)) = 1 :=
  (coordinateWeightEquiv G (G.rootCharacter r)).finrank_eq.trans
    (G.rootWeightSpace_finrank r)

private theorem rawCharacter_injective (a b : adjointWeightIndex G.torusSplit)
    (ha : a.1 ≠ 1) (hab : a.1 = b.1) : a = b := by
  rcases a with ⟨alpha, a⟩
  rcases b with ⟨beta, b⟩
  dsimp only at ha hab
  subst beta
  have hr := rawWeightRoot_character G ⟨alpha, a⟩ ha
  have hd := coordinateRoot_finrank G (rawWeightRoot G ⟨alpha, a⟩ ha)
  rw [hr] at hd
  have ha' : a.val < 1 := by simpa only [hd] using a.isLt
  have hb' : b.val < 1 := by simpa only [hd] using b.isLt
  have hab' : a = b := by
    apply Fin.ext
    omega
  exact congrArg (Sigma.mk alpha) hab'

private theorem rootCharacter_injective : Function.Injective G.rootCharacter := by
  intro r s hrs
  apply G.characterRootEquiv.symm.injective
  exact Subtype.ext hrs

private def rootAt (i : Fin (adjointWeightRank G.torusSplit))
    (hi : adjointWeightCharacter G.torusSplit i ≠ 1) : G.rootIndex :=
  rawWeightRoot G ((Fintype.equivFin (adjointWeightIndex G.torusSplit)).symm i) hi

private theorem rootAt_character (i : Fin (adjointWeightRank G.torusSplit))
    (hi : adjointWeightCharacter G.torusSplit i ≠ 1) :
    G.rootCharacter (rootAt G i hi) = adjointWeightCharacter G.torusSplit i :=
  rawWeightRoot_character G _ hi

private theorem rootAt_injective
    (i j : Fin (adjointWeightRank G.torusSplit))
    (hi : adjointWeightCharacter G.torusSplit i ≠ 1)
    (hj : adjointWeightCharacter G.torusSplit j ≠ 1)
    (hij : rootAt G i hi = rootAt G j hj) : i = j := by
  apply (Fintype.equivFin (adjointWeightIndex G.torusSplit)).symm.injective
  apply rawCharacter_injective G _ _ hi
  exact (rootAt_character G i hi).symm.trans
    ((congrArg G.rootCharacter hij).trans (rootAt_character G j hj))

private theorem rootAt_surjective (r : G.rootIndex) :
    ∃ (i : Fin (adjointWeightRank G.torusSplit)) (hi : adjointWeightCharacter G.torusSplit i ≠ 1),
      rootAt G i hi = r := by
  let a : adjointWeightIndex G.torusSplit :=
    ⟨G.rootCharacter r, ⟨0, by rw [coordinateRoot_finrank G r]; omega⟩⟩
  let i := Fintype.equivFin (adjointWeightIndex G.torusSplit) a
  have hc : adjointWeightCharacter G.torusSplit i = G.rootCharacter r := by
    simp only [adjointWeightCharacter, i, Equiv.symm_apply_apply, a]
  have hi : adjointWeightCharacter G.torusSplit i ≠ 1 :=
    fun he => G.rootCharacter_ne_one r (hc.symm.trans he)
  refine ⟨i, hi, ?_⟩
  apply rootCharacter_injective G
  exact (rootAt_character G i hi).trans hc

private def weightHeight (i : Fin (adjointWeightRank G.torusSplit)) : ℤ :=
  if hi : adjointWeightCharacter G.torusSplit i = 1 then 0 else G.rootBase.height (rootAt G i hi)

private def positiveWeightLabels : Finset (Fin (adjointWeightRank G.torusSplit)) :=
  Finset.univ.filter (fun i => 0 < weightHeight G i)

private theorem positiveWeightLabel_ne_one (i : Fin (adjointWeightRank G.torusSplit))
    (hi : i ∈ positiveWeightLabels G) : adjointWeightCharacter G.torusSplit i ≠ 1 := by
  intro hc
  have hp : 0 < weightHeight G i := (Finset.mem_filter.mp hi).2
  simp only [weightHeight, dite_eq_left hc] at hp
  omega

private theorem positiveWeightLabel_root (i : Fin (adjointWeightRank G.torusSplit))
    (hi : i ∈ positiveWeightLabels G) :
    G.rootBase.IsPos (rootAt G i (positiveWeightLabel_ne_one G i hi)) := by
  have hp : 0 < weightHeight G i := (Finset.mem_filter.mp hi).2
  apply (G.rootBase.isPos_iff).mpr
  simpa only [weightHeight, dite_eq_right (positiveWeightLabel_ne_one G i hi)] using hp

private theorem positiveWeightLabels_card :
    (positiveWeightLabels G).card = Module.finrank K G.unipotentTangent := by
  classical
  let := Fintype.ofFinite G.rootIndex
  let := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let := Fintype.ofFinite (borelRootCharacterIndex G.borelIdeal G.torusSplit)
  have hcard : (positiveWeightLabels G).card =
      (Finset.univ.filter G.rootBase.IsPos).card := by
    apply Finset.card_bij
      (fun i hi => rootAt G i (positiveWeightLabel_ne_one G i hi))
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, positiveWeightLabel_root G i hi⟩
    · intro i hi j hj hij
      exact rootAt_injective G i j _ _ hij
    · intro r hr
      obtain ⟨i, hi, hir⟩ := rootAt_surjective G r
      have hpi : i ∈ positiveWeightLabels G := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [weightHeight, dite_eq_right hi, hir]
        exact G.rootBase.isPos_iff.mp (Finset.mem_filter.mp hr).2
      exact ⟨i, hpi, by simpa only using hir⟩
  have hdim : Module.finrank K G.unipotentTangent =
      Fintype.card (borelRootCharacterIndex G.borelIdeal G.torusSplit) :=
    Module.finrank_eq_card_basis G.borelRootBasis
  have he := Fintype.card_congr G.borelCharacterRootEquiv
  rw [hcard, hdim, he]
  exact (Fintype.card_subtype G.rootBase.IsPos).symm

/-- A degree-N basis selection has maximal height only for all positive-root labels.
The full identity-character fibre remains in the ambient basis throughout. -/
theorem determinantSelection_height_max
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    (∑ i ∈ s.val, weightHeight G i) ≤
        ∑ i ∈ positiveWeightLabels G, weightHeight G i ∧
      ((∑ i ∈ s.val, weightHeight G i) =
          ∑ i ∈ positiveWeightLabels G, weightHeight G i ↔
        s.val = positiveWeightLabels G) := by
  have hc : s.val.card = (positiveWeightLabels G).card :=
    s.property.trans (positiveWeightLabels_card G).symm
  exact FrobeniusSplitting.positive_sum_max (weightHeight G) s.val hc

private def selectionRootMultiplicity (s : Finset (Fin (adjointWeightRank G.torusSplit))) :
    G.rootIndex →₀ ℤ :=
  ∑ i ∈ s, if hi : adjointWeightCharacter G.torusSplit i = 1 then 0
    else Finsupp.single (rootAt G i hi) 1

private def rootCharacterSum : (G.rootIndex →₀ ℤ) →+ Additive G.characters :=
  Finsupp.liftAddHom fun r =>
    { toFun := fun z => Additive.ofMul (G.rootCharacter r ^ z)
      map_zero' := by simp
      map_add' := by intro a b; simp only [zpow_add]; rfl }

private def rootHeightSum : (G.rootIndex →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun r =>
    { toFun := fun z => z * G.rootBase.height r
      map_zero' := zero_mul _
      map_add' := fun a b => add_mul a b _ }

private theorem rootCharacterSum_apply (m : G.rootIndex →₀ ℤ) :
    Additive.toMul (rootCharacterSum G m) =
      m.prod (fun r z => G.rootCharacter r ^ z) := by
  change (∑ r ∈ m.support, Additive.ofMul (G.rootCharacter r ^ m r)).toMul =
    ∏ r ∈ m.support, G.rootCharacter r ^ m r
  rw [toMul_sum]
  rfl

private theorem rootCharacterSum_single (r : G.rootIndex) (z : ℤ) :
    Additive.toMul (rootCharacterSum G (Finsupp.single r z)) = G.rootCharacter r ^ z := by
  rw [rootCharacterSum, Finsupp.liftAddHom_apply_single]
  rfl

private theorem rootHeightSum_apply (m : G.rootIndex →₀ ℤ) :
    rootHeightSum G m = m.sum (fun r z => z * G.rootBase.height r) := rfl

private theorem selectionRootMultiplicity_character
    (s : Finset (Fin (adjointWeightRank G.torusSplit))) :
    Additive.toMul (rootCharacterSum G (selectionRootMultiplicity G s)) =
      ∏ i ∈ s, adjointWeightCharacter G.torusSplit i := by
  classical
  rw [selectionRootMultiplicity, map_sum, toMul_sum]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs with hc
  · simp only [map_zero, toMul_zero, hc]
  · rw [rootCharacterSum, Finsupp.liftAddHom_apply_single]
    change G.rootCharacter (rootAt G i hc) ^ (1 : ℤ) = adjointWeightCharacter G.torusSplit i
    rw [zpow_one]
    exact rootAt_character G i hc

private theorem selectionRootMultiplicity_height
    (s : Finset (Fin (adjointWeightRank G.torusSplit))) :
    rootHeightSum G (selectionRootMultiplicity G s) = ∑ i ∈ s, weightHeight G i := by
  classical
  rw [selectionRootMultiplicity, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with hc
  · simp only [map_zero, weightHeight, dite_eq_left hc]
  · rw [rootHeightSum, Finsupp.liftAddHom_apply_single]
    change 1 * G.rootBase.height (rootAt G i hc) = weightHeight G i
    rw [one_mul, weightHeight, dite_eq_right hc]

private theorem positiveWeightLabels_character :
    (∏ i ∈ positiveWeightLabels G, adjointWeightCharacter G.torusSplit i) =
      G.positiveRootCharacter := by
  classical
  let := Fintype.ofFinite G.rootIndex
  change (∏ i ∈ positiveWeightLabels G, adjointWeightCharacter G.torusSplit i) =
    ∏ r ∈ Finset.univ.filter G.rootBase.IsPos, G.rootCharacter r
  apply Finset.prod_bij
    (fun i hi => rootAt G i (positiveWeightLabel_ne_one G i hi))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, positiveWeightLabel_root G i hi⟩
  · intro i hi j hj hij
    exact rootAt_injective G i j _ _ hij
  · intro r hr
    obtain ⟨i, hi, hir⟩ := rootAt_surjective G r
    have hpi : i ∈ positiveWeightLabels G := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [weightHeight, dite_eq_right hi, hir]
      exact G.rootBase.isPos_iff.mp (Finset.mem_filter.mp hr).2
    exact ⟨i, hpi, by simpa only using hir⟩
  · intro i hi
    exact (rootAt_character G i (positiveWeightLabel_ne_one G i hi)).symm

private theorem selectionRootMultiplicity_relation
    (s : Finset (Fin (adjointWeightRank G.torusSplit)))
    (hs : (∏ i ∈ s, adjointWeightCharacter G.torusSplit i) = G.positiveRootCharacter) :
    (selectionRootMultiplicity G s -
      selectionRootMultiplicity G (positiveWeightLabels G)).prod
        (fun r z => G.rootCharacter r ^ z) = 1 := by
  rw [← rootCharacterSum_apply, map_sub, toMul_sub,
    selectionRootMultiplicity_character, selectionRootMultiplicity_character,
    hs, positiveWeightLabels_character, div_self']

private def positiveSelection :
    Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) (Module.finrank K G.unipotentTangent) :=
  ⟨positiveWeightLabels G, positiveWeightLabels_card G⟩

private theorem positiveSelection_character :
    determinantExteriorCharacter G (positiveSelection G) = G.positiveRootCharacter :=
  positiveWeightLabels_character G

private theorem selection_height_eq_of_character
    (s : Finset (Fin (adjointWeightRank G.torusSplit)))
    (hs : (∏ i ∈ s, adjointWeightCharacter G.torusSplit i) = G.positiveRootCharacter) :
    (∑ i ∈ s, weightHeight G i) =
      ∑ i ∈ positiveWeightLabels G, weightHeight G i := by
  have h := G.rootCharacter_height
    (selectionRootMultiplicity G s -
      selectionRootMultiplicity G (positiveWeightLabels G))
    (selectionRootMultiplicity_relation G s hs)
  change rootHeightSum G
    (selectionRootMultiplicity G s -
      selectionRootMultiplicity G (positiveWeightLabels G)) = 0 at h
  rw [map_sub, selectionRootMultiplicity_height, selectionRootMultiplicity_height] at h
  exact sub_eq_zero.mp h

private theorem selection_character_eq_delta_iff
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent)) :
    determinantExteriorCharacter G s = G.positiveRootCharacter ↔
      s = positiveSelection G := by
  constructor
  · intro hs
    apply Subtype.ext
    exact (determinantSelection_height_max G s).2.mp
      (selection_height_eq_of_character G s.val hs)
  · rintro rfl
    exact positiveSelection_character G

private theorem selection_simple_domination
    (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.unipotentTangent))
    (i : G.rootBase.support) (j : ℤ)
    (hs : determinantExteriorCharacter G s =
      G.positiveRootCharacter * G.rootCharacter i.val ^ j) : j ≤ 0 := by
  let m := selectionRootMultiplicity G s.val -
    selectionRootMultiplicity G (positiveWeightLabels G) - Finsupp.single i.val j
  have hm : m.prod (fun r z => G.rootCharacter r ^ z) = 1 := by
    rw [← rootCharacterSum_apply]
    simp only [m, map_sub, toMul_sub, selectionRootMultiplicity_character,
      positiveWeightLabels_character, rootCharacterSum_single]
    change (determinantExteriorCharacter G s / G.positiveRootCharacter) /
      G.rootCharacter i.val ^ j = 1
    rw [hs]
    simp only [mul_div_cancel_left, div_self']
  have hh := G.rootCharacter_height m hm
  change rootHeightSum G m = 0 at hh
  simp only [m, map_sub, selectionRootMultiplicity_height] at hh
  rw [rootHeightSum, Finsupp.liftAddHom_apply_single] at hh
  change (∑ k ∈ s.val, weightHeight G k) -
    (∑ k ∈ positiveWeightLabels G, weightHeight G k) -
      j * G.rootBase.height i.val = 0 at hh
  rw [G.rootBase.height_one_of_mem_support i.property, mul_one] at hh
  have hmax := (determinantSelection_height_max G s).1
  omega

omit [IsAlgClosed K] [CharZero K] in
private theorem vector_eq_smul_of_coordinates {I V : Type*}
    [AddCommGroup V] [Module K V] (b : Module.Basis I K V) (v : V) (s : I)
    (hv : ∀ t, t ≠ s → b.repr v t = 0) : v = (b.repr v s) • b s := by
  classical
  apply b.repr.injective
  ext t
  by_cases hts : t = s
  · subst t
    simp
  · simp [hv t hts, hts]

omit [CharZero K] in
/-- Distinct torus characters have zero coordinates in a simultaneous character eigenvector. -/
theorem coordinate_vanishes_of_points {I V : Type*}
    [AddCommGroup V] [Module K V] (b : Module.Basis I K V)
    (wt : I → G.characters)
    (rho : (MonoidAlgebra K G.characters →ₐ[K] K) → V →ₗ[K] V)
    (hb : ∀ z i, rho z (b i) = z (MonoidAlgebra.single (wt i) (1 : K)) • b i)
    (v : V) (chi : G.characters)
    (hv : ∀ z, rho z v = z (MonoidAlgebra.single chi (1 : K)) • v)
    (s : I) (hs : wt s ≠ chi) : b.repr v s = 0 := by
  classical
  let : Algebra.FiniteType K (MonoidAlgebra K G.characters) :=
    Algebra.FiniteType.of_surjective G.torusSplit.toAlgHom G.split_surjective
  have hc : (b.repr v s) • MonoidAlgebra.single (wt s) (1 : K) =
      (b.repr v s) • MonoidAlgebra.single chi (1 : K) := by
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
    intro z
    have hL : (b.coord s).comp (rho z) =
        z (MonoidAlgebra.single (wt s) (1 : K)) • b.coord s := by
      apply b.ext
      intro t
      rw [LinearMap.comp_apply, hb, map_smul]
      by_cases hts : t = s
      · subst t
        simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_same, smul_eq_mul, mul_one, LinearMap.smul_apply]
      · simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne' hts, smul_zero, LinearMap.smul_apply]
    have hz := LinearMap.congr_fun hL v
    have he := congrArg (b.coord s) (hv z)
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      map_smul, smul_eq_mul, mul_comm] using hz.symm.trans he
  have he := congrArg (fun z : MonoidAlgebra K G.characters => z.coeff (wt s)) hc
  simpa only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hs, smul_eq_mul, mul_one, mul_zero] using he

/-- Every top Borel exterior vector with its determinant action has weight `2ρ`. -/
theorem borelTop_mem_weight
    (w : ⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
    (hdet : ∀ (e : G.tangent ≃ₗ[K] G.tangent)
      (hB : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
      exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule) e.toLinearMap w =
        LinearMap.det (e.ofSubmodules G.borelTangent.toSubmodule
          G.borelTangent.toSubmodule hB).toLinearMap • w) :
    let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
    let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra)
      (V := G.tangent) (Module.finrank K G.borelTangent.toSubmodule)
    w ∈ DiagonalizableGroup.weightSpace
      (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
      G.torusSplit.toCoalgHom G.positiveRootCharacter := by
  classical
  let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra)
    (V := G.tangent) (Module.finrank K G.borelTangent.toSubmodule)
  let b := (adjointWeightBasis G.torusSplit).exteriorPower
    (Module.finrank K G.borelTangent.toSubmodule)
  let wt (s : Set.powersetCard (Fin (adjointWeightRank G.torusSplit))
      (Module.finrank K G.borelTangent.toSubmodule)) : G.characters :=
    ∏ i ∈ s.val, adjointWeightCharacter G.torusSplit i
  have hb (s) : b s ∈ DiagonalizableGroup.weightSpace _ G.torusSplit.toCoalgHom (wt s) :=
    @exteriorBasis_weightSpace.{u,u,u,u} K G.coordinateAlgebra G.tangent G.characters
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)) inferInstance
      (adjointWeightRank G.torusSplit) G.torusSplit (adjointWeightBasis G.torusSplit)
      (adjointWeightCharacter G.torusSplit) (adjointWeightBasis_weightSpace G.torusSplit)
      (Module.finrank K G.borelTangent.toSubmodule) s
  let rho := fun z : MonoidAlgebra K G.characters →ₐ[K] K =>
    Comodule.basePointsRepresentation (H := G.coordinateAlgebra)
      (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
      (AlgHom.mapDomain G.torusSplit (WithConv.toConv z))
  have hdiag (z) (s) : rho z (b s) =
      z (MonoidAlgebra.single (wt s) (1 : K)) • b s := by
    rw [Comodule.basePointsRepresentation_apply]
    change TensorProduct.lid K _ (Comodule.endOfPoint _
      (z.comp G.torusSplit.toAlgHom) (1 ⊗ₜ[K] b s)) = _
    rw [DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace _
      G.torusSplit z 1 (hb s), one_mul]
    exact TensorProduct.lid_tmul (b s) _
  have hv (z) : rho z w = z (MonoidAlgebra.single G.positiveRootCharacter 1) • w := by
    dsimp only [rho]
    rw [exteriorPower_basePoints, Representation.exteriorPower_apply,
      affineGroupAdjointComodule_points]
    exact DeterminantSection.borelTop_torus G w hdet (WithConv.toConv z)
  rw [← b.sum_repr w]
  apply Submodule.sum_mem
  intro s _
  by_cases hs : wt s = G.positiveRootCharacter
  · rw [← hs]
    exact Submodule.smul_mem _ _ (hb s)
  · have hz := coordinate_vanishes_of_points G b wt rho hdiag w
      G.positiveRootCharacter hv s hs
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

private theorem determinant_positive_weight_basis :
    let := DeterminantSection.adjointExteriorComodule G
    DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom G.positiveRootCharacter =
      Submodule.span K {determinantExteriorBasis G (positiveSelection G)} := by
  let := DeterminantSection.adjointExteriorComodule G
  apply le_antisymm
  · intro v hv
    have hc (s) (hs : s ≠ positiveSelection G) :
        (determinantExteriorBasis G).repr v s = 0 := by
      apply exterior_coordinate_vanishes G G.positiveRootCharacter v s _ hv
      exact fun he => hs ((selection_character_eq_delta_iff G s).mp he)
    exact Submodule.mem_span_singleton.mpr
      ⟨_, (vector_eq_smul_of_coordinates (determinantExteriorBasis G) v
        (positiveSelection G) hc).symm⟩
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    have hp := determinantExteriorBasis_mem_weight G (positiveSelection G)
    rw [positiveSelection_character] at hp
    change determinantExteriorBasis G (positiveSelection G) ∈
      DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom G.positiveRootCharacter
    exact hp

/-- The full-delta weight line is the determinant line of the positive-root tangent space. -/
theorem determinant_positive_weight_line :
    let := DeterminantSection.adjointExteriorComodule G
    DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom G.positiveRootCharacter =
      Submodule.span K {DeterminantSection.positiveDetVector G} := by
  let := DeterminantSection.adjointExteriorComodule G
  dsimp only
  let v := DeterminantSection.positiveDetVector G
  let b := determinantExteriorBasis G
  have hc (s) (hs : s ≠ positiveSelection G) : b.repr v s = 0 := by
    apply coordinate_vanishes_of_points G b (determinantExteriorCharacter G)
      (fun z => Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _
        (AlgHom.mapDomain G.torusSplit (WithConv.toConv z)))
      (fun z t => determinantExteriorBasis_points G (WithConv.toConv z) t)
      v G.positiveRootCharacter
      (fun z => DeterminantSection.positiveDet_torus G (WithConv.toConv z)) s
    exact fun he => hs ((selection_character_eq_delta_iff G s).mp he)
  have he := vector_eq_smul_of_coordinates b v (positiveSelection G) hc
  have hn : b.repr v (positiveSelection G) ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact DeterminantSection.positiveDet_ne_zero G he
  rw [determinant_positive_weight_basis]
  change Submodule.span K {b (positiveSelection G)} = Submodule.span K {v}
  rw [he]
  exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hn) _).symm

/-- An occurring exterior weight cannot lie above delta along a simple root. -/
theorem determinant_positive_simple_domination (i : G.rootBase.support) (j : ℤ) :
    let := DeterminantSection.adjointExteriorComodule G
    DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom
        (G.positiveRootCharacter * G.rootCharacter i.val ^ j) ≠ ⊥ → j ≤ 0 := by
  let := DeterminantSection.adjointExteriorComodule G
  dsimp only
  intro hocc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hocc
  have hex : ∃ s, (determinantExteriorBasis G).repr v s ≠ 0 := by
    by_contra! h
    apply hv0
    apply (determinantExteriorBasis G).repr.injective
    ext s
    simp only [h s, map_zero, Finsupp.zero_apply]
  obtain ⟨s, hs⟩ := hex
  have hc : determinantExteriorCharacter G s =
      G.positiveRootCharacter * G.rootCharacter i.val ^ j := by
    by_contra hn
    exact hs (exterior_coordinate_vanishes G _ v s hn hv)
  exact selection_simple_domination G s i j hc

end SchubertGeometry.DeterminantWeights
