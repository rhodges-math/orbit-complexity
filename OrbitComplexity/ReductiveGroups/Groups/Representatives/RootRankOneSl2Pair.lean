import OrbitComplexity.ReductiveGroups.Groups.Representatives.ReductiveRootReflectionPoint
import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterRootIntegration
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterWeightDifferential

/-!
# Root Rank One Sl 2 Pair

`sl₂`-normalized pairs of additive root subgroups.

For a character `α` of the fixed split torus, a pair `(x, y)` of `Ga`
morphisms into the original group is `sl₂`-normalized when the tangent of `x`
lies in the `α` character space, the tangent of `y` lies in the `α⁻¹`
character space, `(⁅dx, dy⁆, dx, dy)` is an `sl₂` triple, and `⁅dx, dy⁆` lies in
the tangent image of the torus. The root value `dα(⁅dx, dy⁆) = 2` and `α ≠ 1`
are then consequences.

For the original reductive group with a maximal torus, every nonidentity
occurring character `α` and every `Ga` morphism `x` with nonzero tangent in the
`α` space admit a partner `y`. It is obtained from the existing root `sl₂`
triple by one-dimensionality of the `α` space and inverse scaling. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieModule

universe u
variable {K B ι : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- A vector in the `α` character space is an exact eigenvector for
every vector `t` of the torus tangent image, with eigenvalue `dα(t)`. -/
theorem RootRankOneSl2Pair.eq_smul_of_mem_characterWeight
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (α : M)
    (d : 𝔤) (hd : d ∈ affineGroupCharacterWeightSpace π α)
    (t : diagonalizableTangentImage π) :
    ⁅(t : 𝔤), d⁆ = characterDifferentialOnImage π hπ α t • d := by
  obtain ⟨h, hh⟩ := (diagonalizableTangentEquivImage π hπ).surjective t
  have ht : (t : 𝔤) = TauCeti.derivationComp (B := K) π h := by
    rw [← hh]
    rfl
  rw [ht, bracket_eq_character_derivative π α h d hd, ← hh]
  congr 1
  exact (characterDifferentialOnImage_apply_equiv π hπ α h).symm

omit [Algebra.FiniteType K B] in
/-- The differential of an inverse character is the negated differential. -/
theorem characterDifferentialOnImage_inv
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (α : M) :
    characterDifferentialOnImage π hπ α⁻¹ = -characterDifferentialOnImage π hπ α := by
  simp only [characterDifferentialOnImage, characterDifferential_inv]
  rfl

/-- Scaling `e` by a nonzero `c` and `f` by `c⁻¹` preserves an `sl₂` triple. -/
theorem isSl2Triple_smul_smul_inv {L : Type*} [LieRing L] [LieAlgebra K L]
    {h e f : L} (hs : IsSl2Triple h e f) {c : K} (hc : c ≠ 0) :
    IsSl2Triple h (c • e) (c⁻¹ • f) where
  h_ne_zero := hs.h_ne_zero
  lie_e_f := by
    rw [smul_lie, lie_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, hs.lie_e_f]
  lie_h_e_nsmul := by rw [lie_smul, hs.lie_h_e_nsmul, smul_comm]
  lie_h_f_nsmul := by rw [lie_smul, hs.lie_h_f_nsmul, smul_neg, smul_comm]

/-- `(x, y)` is an `sl₂`-normalized pair of additive subgroups for the
torus character `α`: `dx` lies in the `α` character space, `dy` in the `α⁻¹`
character space, `(⁅dx, dy⁆, dx, dy)` is an `sl₂` triple, and `⁅dx, dy⁆` lies in
the tangent image of the torus. -/
structure IsRootSl2Pair (π : B →ₐc[K] MonoidAlgebra K M) (α : M)
    (x y : B →ₐc[K] SymmetricAlgebra K K) : Prop where
  tangent_mem : gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α
  partner_tangent_mem : gaAffineGroupTangent y ∈ affineGroupCharacterWeightSpace π α⁻¹
  isSl2Triple : IsSl2Triple ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆
    (gaAffineGroupTangent x) (gaAffineGroupTangent y)
  bracket_mem : ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆ ∈ diagonalizableTangentImage π

namespace IsRootSl2Pair

variable {π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))}
  {α : Multiplicative (ι →₀ ℤ)} {x y : B →ₐc[K] SymmetricAlgebra K K}

/-- The first tangent of an `sl₂`-normalized pair is nonzero. -/
theorem tangent_ne_zero (hp : IsRootSl2Pair π α x y) : gaAffineGroupTangent x ≠ 0 :=
  hp.isSl2Triple.e_ne_zero

/-- The partner tangent of an `sl₂`-normalized pair is nonzero. -/
theorem partner_tangent_ne_zero (hp : IsRootSl2Pair π α x y) : gaAffineGroupTangent y ≠ 0 :=
  hp.isSl2Triple.f_ne_zero

/-- The character `α` of an `sl₂`-normalized pair occurs. -/
theorem characterWeightSpace_ne_bot (hp : IsRootSl2Pair π α x y) :
    affineGroupCharacterWeightSpace π α ≠ ⊥ := by
  intro hz
  apply hp.tangent_ne_zero
  have hm := hp.tangent_mem
  rw [hz] at hm
  exact (Submodule.mem_bot K).mp hm

/-- The inverse character `α⁻¹` of an `sl₂`-normalized pair occurs. -/
theorem partner_characterWeightSpace_ne_bot (hp : IsRootSl2Pair π α x y) :
    affineGroupCharacterWeightSpace π α⁻¹ ≠ ⊥ := by
  intro hz
  apply hp.partner_tangent_ne_zero
  have hm := hp.partner_tangent_mem
  rw [hz] at hm
  exact (Submodule.mem_bot K).mp hm

/-- The root value at the bracket element of an `sl₂`-normalized pair is `2`. -/
theorem characterDifferential_bracket (hp : IsRootSl2Pair π α x y)
    (hπ : Function.Surjective π) :
    characterDifferentialOnImage π hπ α ⟨_, hp.bracket_mem⟩ = 2 := by
  have hbr := RootRankOneSl2Pair.eq_smul_of_mem_characterWeight π hπ α _ hp.tangent_mem
    ⟨_, hp.bracket_mem⟩
  rw [hp.isSl2Triple.lie_h_e_smul K] at hbr
  exact smul_left_injective K hp.isSl2Triple.e_ne_zero hbr.symm

/-- The character of an `sl₂`-normalized pair is not the identity character
(in characteristic zero). -/
theorem ne_one [CharZero K] (hp : IsRootSl2Pair π α x y) (hπ : Function.Surjective π) :
    α ≠ 1 := by
  intro h1
  have h2 := hp.characterDifferential_bracket hπ
  subst h1
  simp only [characterDifferentialOnImage_one, LinearMap.zero_apply] at h2
  exact two_ne_zero h2.symm

end IsRootSl2Pair

variable [IsAlgClosed K] [CharZero K] [Finite ι]

/-- **`sl₂` partner.** In the original reductive group with maximal torus `I`
(split by `π` with kernel `I`), let `α ≠ 1` be an occurring character and `x`
any `Ga` morphism whose tangent is a nonzero vector of the `α` character
space. Then there is a `Ga` morphism `y` whose tangent is a nonzero
vector of the `α⁻¹` character space such that `(⁅dx, dy⁆, dx, dy)` is an `sl₂`
triple, `⁅dx, dy⁆` lies in the torus tangent image, and `dα(⁅dx, dy⁆) = 2`. -/
theorem exists_sl2Partner
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : M) (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) (hα : α ≠ 1)
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α)
    (hx0 : gaAffineGroupTangent x ≠ 0) :
    ∃ y : B →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupTangent y ∈ affineGroupCharacterWeightSpace π α⁻¹ ∧
      gaAffineGroupTangent y ≠ 0 ∧
      IsSl2Triple ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆
        (gaAffineGroupTangent x) (gaAffineGroupTangent y) ∧
      ∃ hh : ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆ ∈ diagonalizableTangentImage π,
        characterDifferentialOnImage π hπ α ⟨_, hh⟩ = 2 := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let χs := nonidentityCharacterLieWeightEquiv π hπ ⟨α, hocc, hα⟩
  obtain ⟨h, e, f, hs, he, hf, hh⟩ := centralRadical_exists_isSl2Triple H χs.val χs.property
  have hχ : (χs.val : H → K) = characterDifferentialOnImage π hπ α := by
    funext t
    exact nonidentityCharacterLieWeightEquiv_apply π hπ ⟨α, hocc, hα⟩ t
  have he' : e ∈ affineGroupCharacterWeightSpace π α := by
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α, ← hχ]
    exact he
  have hf' : f ∈ affineGroupCharacterWeightSpace π α⁻¹ := by
    have hneg : (characterDifferentialOnImage π hπ α⁻¹ : H → K) = -(χs.val : H → K) := by
      rw [characterDifferentialOnImage_inv, hχ]
      rfl
    rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α⁻¹, hneg]
    exact hf
  have hfin := ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB α hα
    hocc
  have he0 : (⟨e, he'⟩ : affineGroupCharacterWeightSpace π α) ≠ 0 := by
    intro hz
    exact hs.e_ne_zero (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ he0).mp hfin ⟨gaAffineGroupTangent x, hx⟩
  have hce : c • e = gaAffineGroupTangent x := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hx0 (congrArg Subtype.val hc).symm
  have hfmem : c⁻¹ • f ∈ affineGroupCharacterWeightSpace π α⁻¹ :=
    Submodule.smul_mem _ _ hf'
  obtain ⟨y, hy, _⟩ :=
    CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ α⁻¹ (inv_ne_one.mpr hα) _
      hfmem
  have hs' : IsSl2Triple h (gaAffineGroupTangent x) (gaAffineGroupTangent y) := by
    rw [hy, ← hce]
    exact isSl2Triple_smul_smul_inv hs hc0
  have hbr : ⁅gaAffineGroupTangent x, gaAffineGroupTangent y⁆ = h := hs'.lie_e_f
  have hyne : gaAffineGroupTangent y ≠ 0 := hs'.f_ne_zero
  refine ⟨y, hy ▸ hfmem, hyne, hbr ▸ hs', ?_⟩
  rw [hbr]
  refine ⟨hh, ?_⟩
  rw [← hχ]
  exact centralRadical_sl2_root_apply_eq_two H χs.val χs.property hs he hh

/-- Packaged form of `exists_sl2Partner`: every `Ga` morphism with
nonzero tangent in the space of an occurring nonidentity character `α` is the
first member of an `sl₂`-normalized pair for `α`. -/
theorem exists_isRootSl2Pair_of_tangent
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : M) (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) (hα : α ≠ 1)
    (x : B →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α)
    (hx0 : gaAffineGroupTangent x ≠ 0) :
    ∃ y : B →ₐc[K] SymmetricAlgebra K K, IsRootSl2Pair π α x y := by
  obtain ⟨y, hy, -, hs, hh, -⟩ := exists_sl2Partner I hI π hπ hker hB α hocc hα x hx hx0
  exact ⟨y, hx, hy, hs, hh⟩

/-- Every occurring nonidentity character of the maximal torus has an
`sl₂`-normalized pair of `Ga` morphisms. -/
theorem exists_isRootSl2Pair
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : M) (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) (hα : α ≠ 1) :
    ∃ x y : B →ₐc[K] SymmetricAlgebra K K, IsRootSl2Pair π α x y := by
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hocc
  obtain ⟨x, hx, _⟩ := CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ α hα d
    hd
  obtain ⟨y, hy⟩ := exists_isRootSl2Pair_of_tangent I hI π hπ hker hB α hocc hα x
    (hx ▸ hd) (hx ▸ hd0)
  exact ⟨x, y, hy⟩

end ReductiveGroups
