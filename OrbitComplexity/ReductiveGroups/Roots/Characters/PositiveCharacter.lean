import OrbitComplexity.ReductiveGroups.Roots.Characters.PositivePairing
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCorootSquare

/-! # The odd-degree root character in the full torus lattice -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open scoped BigOperators
open Coroot
attribute [local instance] Classical.propDecidable
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The product of all positive root characters in the chosen torus character group. -/
def positiveRootCharacter : G.characters :=
  letI := Fintype.ofFinite G.rootIndex
  ∏ r ∈ Finset.univ.filter G.rootBase.IsPos, G.rootCharacter r

/-- An integer power of the positive-root product, defined without a half-root character. -/
def oddRootCharacter (p : ℕ) : G.characters :=
  G.positiveRootCharacter ^ ((p - 1) / 2)

private theorem coroot_root (i : G.rootBase.support) (r : G.rootIndex) :
    simpleCorootFunctional G i (G.rootCharacter r).toAdd =
      G.rootSystem.pairingIn ℤ r i.val := by
  obtain ⟨l, c, phi, hl, _, _, hr, _, _⟩ := simple_coroot_exists G i
  have he : l (G.rootCharacter r).toAdd =
      simpleCorootFunctional G i (G.rootCharacter r).toAdd := by
    apply Int.cast_injective (α := K)
    rw [hl, simpleCorootFunctional_cast]
  exact he.symm.trans (hr r)

private theorem positive_weight (i : G.rootBase.support) :
    simpleCorootFunctional G i G.positiveRootCharacter.toAdd = 2 := by
  let := Fintype.ofFinite G.rootIndex
  simp only [positiveRootCharacter, toAdd_prod, map_sum]
  simp_rw [coroot_root G i]
  exact positive_pairing_sum G.rootSystem G.rootBase i

/-- At odd degree, every fixed simple coroot has exponent one less than the degree. -/
theorem oddRootCharacter_weight (p : ℕ) (hp : Odd p) (i : G.rootBase.support) :
    simpleCorootFunctional G i (G.oddRootCharacter p).toAdd = (p - 1 : ℕ) := by
  have hnat : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := hp
    omega
  simp only [oddRootCharacter, toAdd_pow, map_nsmul, positive_weight G i,
    nsmul_eq_mul]
  exact_mod_cast (Nat.mul_comm ((p - 1) / 2) 2).trans hnat

/-- Evaluation along the simple coroot retains the full group point and central factors. -/
theorem oddRootCharacter_eval (p : ℕ) (hp : Odd p) (i : G.rootBase.support) (a : Kˣ) :
    (simpleCorootTorusPoint G i a).ofConv
        (MonoidAlgebra.single (G.oddRootCharacter p) 1) = ((a ^ (p - 1) : Kˣ) : K) := by
  rw [simpleCorootTorusPoint_eval, oddRootCharacter_weight G p hp]
  simp only [zpow_natCast]

end ReductiveGroups.ReductiveGroupData
