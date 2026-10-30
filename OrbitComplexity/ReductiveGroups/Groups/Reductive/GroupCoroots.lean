import OrbitComplexity.ReductiveGroups.Groups.Representations.FiniteComoduleActions
import OrbitComplexity.ReductiveGroups.Lie.Roots.Sl2WeylSquare
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Lie
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootPairIndependence
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTorsionTangent
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.Algebra.AlgebraicGroup.Cocharacter
import TauCeti.Algebra.Lie.Sl2.Spectrum
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # The simple coroot on the full torus character lattice -/

noncomputable section

namespace ReductiveGroups.Coroot

open scoped TensorProduct
open TauCeti

section

universe u v w
variable {K : Type u} [Field K] {B : Type v} [CommRing B] [Bialgebra K B]
  {M : Type w} [CommGroup M]

/-- A torus character lifts to a weight vector in a finite regular subcomodule. -/
private theorem exists_character_vector
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (χ : M) :
    ∃ N : Subcomodule K B B, Module.Finite K N.toSubmodule ∧
      ∃ v : N, π (v : B) = MonoidAlgebra.single χ 1 ∧
        v ∈ DiagonalizableGroup.weightSpace N π.toCoalgHom χ := by
  classical
  obtain ⟨b, hb⟩ := hπ (MonoidAlgebra.single χ 1)
  obtain ⟨N, hN, hbN⟩ := Subcomodule.exists_finite_subcomodule_mem
    (R := K) (C := B) (M := B) b
  let : Comodule K (MonoidAlgebra K M) B := Comodule.Corestrict π.toCoalgHom
  let : Comodule K (MonoidAlgebra K M) N := Comodule.Corestrict π.toCoalgHom
  let q : Comodule.Hom K (MonoidAlgebra K M) B (MonoidAlgebra K M) :=
    { toLinearMap := π.toLinearMap
      map_coact := by
        ext b
        change TensorProduct.map π.toLinearMap LinearMap.id
            (TensorProduct.map LinearMap.id π.toLinearMap (Coalgebra.comul b)) =
          Coalgebra.comul (π b)
        rw [TensorProduct.map_map]
        have hc : TensorProduct.map π.toLinearMap π.toLinearMap (Coalgebra.comul b) =
            Coalgebra.comul (π.toLinearMap b) := by
          simpa only [LinearMap.comp_apply] using
            LinearMap.congr_fun π.toCoalgHom.map_comp_comul b
        simpa only [LinearMap.comp_id, LinearMap.id_comp] using
          hc.trans (congrArg Coalgebra.comul (show π.toLinearMap b = π b from rfl)) }
  let j := Comodule.corestrictHom π.toCoalgHom (Subcomodule.subtype N)
  let f : Comodule.Hom K (MonoidAlgebra K M) N (MonoidAlgebra K M) :=
    Comodule.Hom.comp q j
  let v := Comodule.weightProj K M N χ (⟨b, hbN⟩ : N)
  refine ⟨N, hN, v, ?_, ?_⟩
  · have hf := f.map_weightProj χ (⟨b, hbN⟩ : N)
    change π (v : B) = Comodule.weightProj K M (MonoidAlgebra K M) χ (π b) at hf
    rw [hb] at hf
    exact hf.trans (by
      apply Comodule.weightProj_of_mem
      rw [Comodule.mem_weightSpace]
      change Coalgebra.comul (MonoidAlgebra.single χ (1 : K)) = _
      simp)
  · exact Comodule.weightProj_mem_weightSpace χ (⟨b, hbN⟩ : N)
end
section
open LieAlgebra TauCeti Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The Cartan tangent of the fixed positive and negative simple-root pair. -/
def simpleCartan (i : G.rootBase.support) : G.torusTangent :=
  ⟨⁅gaAffineGroupTangent (G.simpleRootMap i),
      gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆,
    (characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus G.torusSplit
      G.split_surjective G.split_eq_zero G.reductive
      (G.characterRootEquiv.symm i.val)).bracket_mem⟩

variable {V : Type v} [AddCommGroup V] [Module K V]
  [Comodule K G.coordinateAlgebra V] {n : ℕ}

/-- A nonzero vector in an occurring torus-character space gives an integral Cartan value. -/
private theorem simple_weight_integral (i : G.rootBase.support) (b : Basis (Fin n) K V)
    (chi : G.characters) (x : V)
    (hx : x ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom chi)
    (hx0 : x ≠ 0) :
    ∃ z : ℤ, characterDifferentialOnImage G.torusSplit G.split_surjective chi
      (simpleCartan G i) = (z : K) := by
  let : Module.Finite K V := Module.Finite.of_basis b
  let : LieRingModule G.tangent V :=
    LieRingModule.compLieHom V (finiteComoduleLie b)
  let : LieModule K G.tangent V :=
    LieModule.compLieHom V (finiteComoduleLie b)
  have hp := characterSl2PairChoice_isRootSl2Pair G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    (G.characterRootEquiv.symm i.val)
  have hw : ⁅(simpleCartan G i : G.tangent), x⁆ =
      characterDifferentialOnImage G.torusSplit G.split_surjective chi
        (simpleCartan G i) • x :=
    finiteComoduleLie_weight_image b G.torusSplit G.split_surjective chi
      (simpleCartan G i) x hx
  exact exists_int_of_lie_h_eq_smul hp.isSl2Triple hw hx0
end
section
open TauCeti Module

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Every character has an integral value on the chosen simple Cartan tangent. -/
private theorem simple_character_integral (i : G.rootBase.support) (chi : G.characters) :
    ∃ z : ℤ, characterDifferentialOnImage G.torusSplit G.split_surjective chi
      (simpleCartan G i) = (z : K) := by
  obtain ⟨N, hN, v, hv, hw⟩ :=
    exists_character_vector
      G.torusSplit G.split_surjective chi
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup K
  let : Module.Finite K N := hN
  let : Module.Free K N := Module.Free.of_divisionRing K N
  have hv0 : v ≠ 0 := by
    intro hz
    have h := hv
    rw [hz, Submodule.coe_zero, map_zero] at h
    exact (MonoidAlgebra.single_ne_zero.mpr one_ne_zero) h.symm
  exact simple_weight_integral G i (Module.finBasis K N) chi v hw hv0

omit [IsAlgClosed K] in
private theorem integral_lift {A : Type*} [AddCommGroup A]
    (d : A →+ K) (hd : ∀ a, ∃ z : ℤ, d a = (z : K)) :
    ∃ l : A →+ ℤ, ∀ a, (l a : K) = d a := by
  classical
  let l : A → ℤ := fun a => Classical.choose (hd a)
  have hl (a : A) : (l a : K) = d a := (Classical.choose_spec (hd a)).symm
  refine ⟨{ toFun := l, map_zero' := ?_, map_add' := ?_ }, hl⟩
  · apply Int.cast_injective (α := K)
    rw [hl, map_zero, Int.cast_zero]
  · intro a b
    apply Int.cast_injective (α := K)
    rw [Int.cast_add, hl, hl, hl, map_add]

/-- The unique integral character functional of the fixed simple Cartan tangent. -/
def simpleCorootFunctional (i : G.rootBase.support) : (G.torusIndex →₀ ℤ) →+ ℤ :=
  Classical.choose (integral_lift
    ((LinearMap.applyₗ (simpleCartan G i)).toAddMonoidHom.comp
      (characterDifferentialOnImageHom G.torusSplit G.split_surjective))
    (fun a => simple_character_integral G i (Multiplicative.ofAdd a)))

/-- Its integer value has the prescribed differential on every torus character. -/
theorem simpleCorootFunctional_cast (i : G.rootBase.support) (a : G.torusIndex →₀ ℤ) :
    (simpleCorootFunctional G i a : K) =
      characterDifferentialOnImage G.torusSplit G.split_surjective
        (Multiplicative.ofAdd a) (simpleCartan G i) :=
  Classical.choose_spec (integral_lift
    ((LinearMap.applyₗ (simpleCartan G i)).toAddMonoidHom.comp
      (characterDifferentialOnImageHom G.torusSplit G.split_surjective))
    (fun a => simple_character_integral G i (Multiplicative.ofAdd a))) a
end
section
open TauCeti WithConv

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The full-lattice integral functional, in multiplicative character notation. -/
def simpleCorootCharacter (i : G.rootBase.support) : G.characters →* Multiplicative ℤ where
  toFun chi := Multiplicative.ofAdd (simpleCorootFunctional G i chi.toAdd)
  map_one' := by
    change Multiplicative.ofAdd (simpleCorootFunctional G i 0) = 1
    rw [map_zero]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (simpleCorootFunctional G i (a.toAdd + b.toAdd)) = _
    rw [map_add]
    rfl

/-- The character functional is the exact integer exponent of the cocharacter. -/
private theorem simpleCorootCharacter_apply (i : G.rootBase.support) (chi : G.characters) :
    (simpleCorootCharacter G i chi).toAdd = simpleCorootFunctional G i chi.toAdd := rfl

/-- The coordinate morphism of the simple coroot into the chosen torus of G. -/
def simpleCorootMap (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] MonoidAlgebra K (Multiplicative ℤ) :=
  (MonoidAlgebra.mapDomainBialgHom K (simpleCorootCharacter G i)).comp G.torusSplit

/-- The torus point of the full-character simple coroot at an arbitrary unit. -/
def simpleCorootTorusPoint (i : G.rootBase.support) (u : Kˣ) :
    WithConv (MonoidAlgebra K G.characters →ₐ[K] K) :=
  DiagonalizableGroup.cocharPoints (simpleCorootCharacter G i)
    ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u))

/-- The group point of the simple coroot at an arbitrary unit. -/
def simpleCorootPoint (i : G.rootBase.support) (u : Kˣ) : G.points :=
  AlgHom.mapDomain G.torusSplit (simpleCorootTorusPoint G i u)

/-- Every full torus character evaluates by its integral Cartan exponent. -/
theorem simpleCorootTorusPoint_eval (i : G.rootBase.support) (u : Kˣ)
    (chi : G.characters) :
    (simpleCorootTorusPoint G i u).ofConv (MonoidAlgebra.single chi 1) =
      ((u ^ (simpleCorootFunctional G i chi.toAdd) : Kˣ) : K) := by
  have h := DiagonalizableGroup.pointsMulEquiv_cocharPoints
    (R := K) (A := K) (simpleCorootCharacter G i)
    ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u)) chi
  rw [simpleCorootCharacter_apply] at h
  simp only [MulEquiv.apply_symm_apply, zpowersHom_apply, toAdd_ofAdd, zpow_one] at h
  exact congrArg (fun z : Kˣ => (z : K)) h

/-- The point construction is induced by the coordinate morphism. -/
theorem simpleCorootPoint_map (i : G.rootBase.support) (u : Kˣ) :
    simpleCorootPoint G i u = AlgHom.mapDomain (simpleCorootMap G i)
      ((DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ u)) := rfl
end
section
open TauCeti

universe u
variable {K : Type u} [Field K]

private def integerCharacter : Multiplicative ℤ →* Multiplicative K where
  toFun m := Multiplicative.ofAdd (m.toAdd : K)
  map_one' := by simp
  map_mul' a b := by simp [Int.cast_add]

/-- The standard tangent generator of the multiplicative group. -/
def multiplicativeTangent :
    Derivation K (MonoidAlgebra K (Multiplicative ℤ))
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative ℤ)) K) :=
  diagonalizableTangentOfAdditive integerCharacter

private theorem mapDomain_character {M N : Type*} [CommGroup M] [CommGroup N]
    (c : M →* N)
    (d : Derivation K (MonoidAlgebra K N)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K N) K)) (chi : M) :
    characterDifferential chi
      (derivationComp (B := K) (MonoidAlgebra.mapDomainBialgHom K c) d) =
      characterDifferential (c chi) d := by
  rw [characterDifferential_apply, characterDifferential_apply,
    algEquivSelf_derivationComp_apply]
  change (Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K N) K)
    (d ((MonoidAlgebra.mapDomainBialgHom K c) (MonoidAlgebra.single chi 1))) = _
  rw [MonoidAlgebra.mapDomainBialgHom_single]

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The coroot differential is the exact bracket of the fixed simple-root tangents. -/
theorem simpleCorootMap_differential (i : G.rootBase.support) :
    derivationComp (B := K) (simpleCorootMap G i) (multiplicativeTangent (K := K)) =
      (simpleCartan G i : G.tangent) := by
  let c := MonoidAlgebra.mapDomainBialgHom K (simpleCorootCharacter G i)
  let ht := (diagonalizableTangentEquivImage G.torusSplit G.split_surjective).symm
    (simpleCartan G i)
  have he : derivationComp (B := K) c (multiplicativeTangent (K := K)) = ht := by
    apply diagonalizableTangent_ext
    intro chi
    rw [mapDomain_character]
    change characterDifferential (simpleCorootCharacter G i chi)
      (diagonalizableTangentOfAdditive integerCharacter) = _
    rw [CharacterDifferential.of_additive_tangent]
    change ((simpleCorootCharacter G i chi).toAdd : K) = _
    rw [simpleCorootCharacter_apply]
    exact simpleCorootFunctional_cast G i chi.toAdd
  have hc := LinearMap.congr_fun (derivationComp_comp (B := K) c G.torusSplit)
    (multiplicativeTangent (K := K))
  rw [LinearMap.comp_apply, he] at hc
  exact hc.trans (congrArg Subtype.val
    ((diagonalizableTangentEquivImage G.torusSplit G.split_surjective).apply_symm_apply
      (simpleCartan G i)))
end
section
open TauCeti LieAlgebra LieModule Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)
  {V : Type v} [AddCommGroup V] [Module K V]
  [Comodule K G.coordinateAlgebra V] {n : ℕ}

/-- The representative square acts by the parity of any full character value. -/
private theorem simple_square_character (i : G.rootBase.support) (b : Basis (Fin n) K V)
    (chi : G.characters) (q : ℤ) (v : V)
    (hv : v ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom chi)
    (hq : characterDifferentialOnImage G.torusSplit G.split_surjective chi
      (simpleCartan G i) = (q : K)) :
    finiteComodulePoints b ((G.reflectionPoint i.val) ^ 2) v = (-1 : K) ^ q • v := by
  let : Module.Finite K V := Module.Finite.of_basis b
  let : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  let rep := (finiteComoduleLie b).comp (G.simpleSl2LieHom i)
  let : LieRingModule (SpecialLinear.sl (Fin 2) K) V := LieRingModule.compLieHom V rep
  let : LieModule K (SpecialLinear.sl (Fin 2) K) V := LieModule.compLieHom V rep
  let E := finiteComoduleLie b (gaAffineGroupTangent (G.simpleRootMap i))
  let F := finiteComoduleLie b (gaAffineGroupTangent (G.negativeSimpleRootMap i))
  let W := IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
  have he : toEnd K (SpecialLinear.sl (Fin 2) K) V (slFinTwoBasis K 0) = E := by
    change finiteComoduleLie b (G.simpleSl2LieHom i (slFinTwoBasis K 0)) = E
    rw [G.simpleSl2LieHom_basis]
    rfl
  have hf : toEnd K (SpecialLinear.sl (Fin 2) K) V (slFinTwoBasis K 1) = F := by
    change finiteComoduleLie b (G.simpleSl2LieHom i (slFinTwoBasis K 1)) = F
    rw [G.simpleSl2LieHom_basis]
    rfl
  have hh : ⁅slFinTwoBasis K 2, v⁆ = (q : K) • v := by
    change finiteComoduleLie b (G.simpleSl2LieHom i (slFinTwoBasis K 2)) v = _
    rw [G.simpleSl2LieHom_basis]
    have hw := finiteComoduleLie_weight_image b G.torusSplit G.split_surjective chi
      (simpleCartan G i) v hv
    rw [hq] at hw
    exact hw
  have sq := Sl2Square.square_on_weight (M := V)
    (by rw [he]; exact finiteComoduleLie_ga_nilpotent b _)
    (by rw [hf]; exact finiteComoduleLie_ga_nilpotent b _) q v hh
  dsimp only at sq
  rw [he, hf] at sq
  have hW (z : V) : finiteComodulePoints b (G.reflectionPoint i.val) z = W z := by
    change finiteComodulePoints b
      (gaParameterPoint (G.simpleRootMap i) 1 *
        gaParameterPoint (G.negativeSimpleRootMap i) (-1) *
        gaParameterPoint (G.simpleRootMap i) 1) z = W z
    have hm : finiteComoduleLie b
        ((-1 : K) • gaAffineGroupTangent (G.negativeSimpleRootMap i)) = -F := by
      exact (congrArg (finiteComoduleLie b)
        (neg_one_smul K (gaAffineGroupTangent (G.negativeSimpleRootMap i)))).trans
          ((finiteComoduleLie b).map_neg _)
    simp only [map_mul, Module.End.mul_apply, finiteComodulePoints_ga, one_smul]
    rw [hm]
    rfl
  rw [map_pow, pow_two, Module.End.mul_apply, hW, hW]
  exact sq
end
section
open TauCeti Module WithConv

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Every torus character reads the exact parity of the simple representative square. -/
theorem square_character_value (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (hz : (G.reflectionPoint i.val) ^ 2 = AlgHom.mapDomain G.torusSplit z)
    (chi : G.characters) :
    z.ofConv (MonoidAlgebra.single chi 1) =
      (-1 : K) ^ simpleCorootFunctional G i chi.toAdd := by
  obtain ⟨N, hN, v, hv, hw⟩ :=
    exists_character_vector
      G.torusSplit G.split_surjective chi
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup K
  let : Module.Finite K N := hN
  let : Module.Free K N := Module.Free.of_divisionRing K N
  have hv0 : v ≠ 0 := by
    intro he
    have h := hv
    rw [he, Submodule.coe_zero, map_zero] at h
    exact (MonoidAlgebra.single_ne_zero.mpr one_ne_zero) h.symm
  let b := Module.finBasis K N
  have hs := simple_square_character G i b chi
    (simpleCorootFunctional G i chi.toAdd) v hw (simpleCorootFunctional_cast G i _).symm
  have ht := finiteComodulePoints_weight b G.torusSplit z chi v hw
  rw [← hz] at ht
  exact smul_left_injective K hv0 (ht.symm.trans hs)

end

end ReductiveGroups.Coroot
