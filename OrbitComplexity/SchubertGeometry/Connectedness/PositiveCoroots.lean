import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositivePairing
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCorootSquare
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# The integral positive-coroot cocharacter

The sum of the positive coroots has integral coordinates in the simple-coroot
basis. Combining the given full-character simple-coroot functionals with
those coefficients defines a cocharacter on the full split torus lattice.

Every root pairs with this cocharacter to twice its original-base height.
The positivity set is the dual root base, so no simply-laced assumption enters.

-/

noncomputable section

open scoped BigOperators
open TauCeti ReductiveGroups

attribute [local instance] Classical.propDecidable

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u v w x

private theorem basis_functional_sum {R I : Type*} [CommRing R] [Fintype I]
    {L : Type*} [AddCommGroup L] [Module R L]
    (b : Module.Basis I R L) (x : L) (f : L →ₗ[R] R) :
    (∑ i, b.repr x i * f (b i)) = f x := by
  have h := congrArg f (b.sum_repr x)
  simpa only [map_sum, map_smul, smul_eq_mul] using h

section RootPairing

variable {ι : Type u} {K : Type v} [Field K] [CharZero K]
  {M : Type w} [AddCommGroup M] [Module K M]
  {N : Type x} [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Fintype ι]
  [P.IsCrystallographic] [P.IsReduced]

omit [Fintype ι] [P.IsReduced] in
private theorem flip_pairing (i j : ι) :
    P.flip.pairingIn ℤ i j = P.pairingIn ℤ j i := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [RootPairing.algebraMap_pairingIn, RootPairing.algebraMap_pairingIn]
  rfl

private theorem simple_coroot_sum (b : P.Base) (i : b.support) :
    ∑ r ∈ Finset.univ.filter b.flip.IsPos, P.pairingIn ℤ i.val r = 2 := by
  have h := positive_pairing_sum P.flip b.flip
    (⟨i.val, i.property⟩ : b.flip.support)
  simp_rw [flip_pairing] at h
  exact h

/-- The sum of the positive coroots evaluates on a root as twice its height. -/
theorem positiveCoroot_height (b : P.Base) (j : ι) :
    ∑ r ∈ Finset.univ.filter b.flip.IsPos, P.pairingIn ℤ j r =
      2 * b.height j := by
  classical
  let L : P.rootSpan ℤ →ₗ[ℤ] ℤ :=
    ∑ r ∈ Finset.univ.filter b.flip.IsPos, P.coroot'In ℤ r
  have hs (i : ι) (hi : i ∈ b.support) : L (P.rootSpanMem ℤ i) = 2 := by
    simpa only [L, LinearMap.sum_apply,
      RootPairing.coroot'In_rootSpanMem_eq_pairingIn] using
      simple_coroot_sum P b ⟨i, hi⟩
  obtain ⟨f, _, _, hf⟩ := b.exists_root_eq_sum_int j
  have hx : P.rootSpanMem ℤ j =
      ∑ i ∈ b.support, f i • P.rootSpanMem ℤ i := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hf
  calc
    ∑ r ∈ Finset.univ.filter b.flip.IsPos, P.pairingIn ℤ j r =
        L (P.rootSpanMem ℤ j) := by
      simp only [L, LinearMap.sum_apply,
        RootPairing.coroot'In_rootSpanMem_eq_pairingIn]
    _ = ∑ i ∈ b.support, f i * 2 := by
      rw [hx, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_zsmul, hs i hi, Int.zsmul_eq_mul]
    _ = (∑ i ∈ b.support, f i) * 2 :=
      (Finset.sum_mul b.support f 2).symm
    _ = 2 * b.height j := by
      rw [← b.height_eq_sum hf, mul_comm]

private def positiveCorootSum (b : P.Base) : P.flip.rootSpan ℤ :=
  ∑ r ∈ Finset.univ.filter b.flip.IsPos, P.flip.rootSpanMem ℤ r

private def corootCoordinate (b : P.Base) (i : b.support) : ℤ :=
  b.flip.toWeightBasisInt.repr (positiveCorootSum P b) i

omit [P.IsReduced] in
private theorem corootCoordinate_pair (b : P.Base) (r : ι) :
    ∑ i : b.support,
      corootCoordinate P b i * P.pairingIn ℤ r i.val =
    ∑ j ∈ Finset.univ.filter b.flip.IsPos, P.pairingIn ℤ r j := by
  classical
  have hb (i : b.flip.support) :
      b.flip.toWeightBasisInt i = P.flip.rootSpanMem ℤ i.val :=
    Subtype.ext (b.flip.coe_toWeightBasisInt_apply i)
  have h := basis_functional_sum b.flip.toWeightBasisInt
    (positiveCorootSum P b) (P.flip.coroot'In ℤ r)
  calc
    _ = ∑ i : b.flip.support,
        b.flip.toWeightBasisInt.repr (positiveCorootSum P b) i *
          (P.flip.coroot'In ℤ r) (b.flip.toWeightBasisInt i) := by
      apply Fintype.sum_equiv
        (show b.support ≃ b.flip.support from Equiv.refl _) _ _
      intro i
      rw [hb, RootPairing.coroot'In_rootSpanMem_eq_pairingIn, flip_pairing]
      rfl
    _ = (P.flip.coroot'In ℤ r) (positiveCorootSum P b) := by
      exact h
    _ = _ := by
      simp only [positiveCorootSum, map_sum,
        RootPairing.coroot'In_rootSpanMem_eq_pairingIn, flip_pairing]

end RootPairing

section ReductiveGroup

open ReductiveGroups.Coroot

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def corootCoefficient (i : G.rootBase.support) : ℤ := by
  let := Fintype.ofFinite G.rootIndex
  exact corootCoordinate G.rootSystem G.rootBase i

private theorem coefficient_pair (r : G.rootIndex) :
    ∑ i : G.rootBase.support,
      corootCoefficient G i * G.rootSystem.pairingIn ℤ r i.val =
    ∑ j ∈ (let := Fintype.ofFinite G.rootIndex
      Finset.univ.filter G.rootBase.flip.IsPos), G.rootSystem.pairingIn ℤ r j := by
  classical
  let := Fintype.ofFinite G.rootIndex
  simpa only [corootCoefficient] using
    corootCoordinate_pair G.rootSystem G.rootBase r

private theorem coroot_root (i : G.rootBase.support) (r : G.rootIndex) :
    simpleCorootFunctional G i (G.rootCharacter r).toAdd =
      G.rootSystem.pairingIn ℤ r i.val := by
  obtain ⟨l, c, phi, hl, _, _, hr, _, _⟩ := simple_coroot_exists G i
  have he : l (G.rootCharacter r).toAdd =
      simpleCorootFunctional G i (G.rootCharacter r).toAdd := by
    apply Int.cast_injective (α := K)
    rw [hl, simpleCorootFunctional_cast]
  exact he.symm.trans (hr r)

private def cocharacterFunctional : (G.torusIndex →₀ ℤ) →+ ℤ where
  toFun chi := ∑ i : G.rootBase.support,
    corootCoefficient G i * simpleCorootFunctional G i chi
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]

/-- The positive-coroot sum as an integral cocharacter of the full character
lattice, including central torus directions. -/
def positiveCocharacter : G.characters →* Multiplicative ℤ :=
  (cocharacterFunctional G).toMultiplicative

/-- Evaluation of the positive cocharacter on the original full character
lattice uses the specified simple-coroot functionals. -/
theorem positiveCocharacter_apply (chi : G.characters) :
    (positiveCocharacter G chi).toAdd =
      ∑ i : G.rootBase.support,
        corootCoefficient G i * simpleCorootFunctional G i chi.toAdd := rfl

/-- Each original root character has twice its integer root height as exponent. -/
theorem positiveCocharacter_root (r : G.rootIndex) :
    (positiveCocharacter G (G.rootCharacter r)).toAdd =
      2 * G.rootBase.height r := by
  classical
  let := Fintype.ofFinite G.rootIndex
  rw [positiveCocharacter_apply]
  simp_rw [coroot_root G]
  exact (coefficient_pair G r).trans
    (positiveCoroot_height G.rootSystem G.rootBase r)

/-- Positive roots have strictly positive cocharacter exponent. -/
theorem positiveCocharacter_pos (r : G.rootIndex) (hr : G.rootBase.IsPos r) :
    0 < (positiveCocharacter G (G.rootCharacter r)).toAdd := by
  rw [positiveCocharacter_root]
  exact mul_pos (by decide : (0 : ℤ) < 2) hr

/-- The coordinate bialgebra map to the multiplicative group induced by the
positive-coroot cocharacter and the original split torus quotient. -/
def positiveCocharacterMap :
    G.coordinateAlgebra →ₐc[K] MonoidAlgebra K (Multiplicative ℤ) :=
  (MonoidAlgebra.mapDomainBialgHom K (positiveCocharacter G)).comp G.torusSplit

end ReductiveGroup

end SchubertGeometry.CellContraction
