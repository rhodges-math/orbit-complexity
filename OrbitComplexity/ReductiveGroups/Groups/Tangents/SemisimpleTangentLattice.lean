import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.Subgroup.Saturated
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Semisimple Tangent Lattice

The integral relations among eigenvalues of a diagonal tangent matrix.
Their quotient lattice has no torsion in characteristic zero. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K ι : Type u} [Field K] [CharZero K]

/-- Additive weight of a Laurent monomial under the diagonal derivation
whose eigenvalues are `eigenvalue`. -/
def diagonalTangentWeight (eigenvalue : ι → K) : (ι →₀ ℤ) →+ K :=
  (Finsupp.linearCombination ℤ eigenvalue).toAddMonoidHom

omit [CharZero K] in
/-- The equality is

```lean
diagonalTangentWeight eigenvalue (Finsupp.single i z) = z • eigenvalue i
```
-/
@[simp] theorem diagonalTangentWeight_single (eigenvalue : ι → K) (i : ι) (z : ℤ) :
    diagonalTangentWeight eigenvalue (Finsupp.single i z) = z • eigenvalue i := by
  simp [diagonalTangentWeight]

/-- The integer relation lattice of diagonal eigenvalues is saturated:
if a nonzero multiple of a Laurent exponent has weight zero, that exponent
already has weight zero. -/
theorem diagonalTangentWeight_ker_saturated (eigenvalue : ι → K) :
    (diagonalTangentWeight eigenvalue).ker.NSMulSaturated :=
  AddSubmonoid.ker_saturated (diagonalTangentWeight eigenvalue)

/-- The relation-lattice quotient injects into the additive group of the
characteristic-zero field and therefore has no integer torsion. -/
theorem DiagonalTangentWeight.quotient_torsionFree (eigenvalue : ι → K) :
    IsAddTorsionFree
      ((ι →₀ ℤ) ⧸ (diagonalTangentWeight eigenvalue).ker) := by
  let e := QuotientAddGroup.quotientKerEquivRange (diagonalTangentWeight eigenvalue)
  refine ⟨?_⟩
  intro n hn a b hab
  apply e.injective
  apply Subtype.ext
  apply (IsAddTorsionFree.nsmul_right_injective (M := K) hn)
  have he := congrArg (fun x : (diagonalTangentWeight eigenvalue).range => (x : K))
    (congrArg e hab)
  have hcoe (x : (diagonalTangentWeight eigenvalue).range) :
      ((n • x : (diagonalTangentWeight eigenvalue).range) : K) = n • (x : K) :=
    ((diagonalTangentWeight eigenvalue).range.subtype).map_nsmul n x
  simpa only [map_nsmul, hcoe] using he

/-- Every homomorphism from a character group to a torsion-free group kills
the character group's torsion. -/
theorem torsion_le_ker_of_torsionFree
    {M N : Type*} [CommGroup M] [CommGroup N] [IsMulTorsionFree N]
    (f : M →* N) : CommGroup.torsion M ≤ f.ker := by
  intro m hm
  have hm' : f m ∈ CommGroup.torsion N := (CommGroup.le_comap_torsion f) hm
  rw [CommGroup.isMulTorsionFree_iff_torsion_eq_bot.mp inferInstance] at hm'
  simpa using hm'

/-- Universal factorization of a character homomorphism through the
torsion-free quotient. -/
def torsionFreeFactor
    {M N : Type*} [CommGroup M] [CommGroup N] [IsMulTorsionFree N]
    (f : M →* N) : (M ⧸ CommGroup.torsion M) →* N :=
  QuotientGroup.lift (CommGroup.torsion M) f (torsion_le_ker_of_torsionFree f)

/-- The equality is

```lean
torsionFreeFactor f (QuotientGroup.mk m) = f m
```
-/
@[simp] theorem torsionFreeFactor_mk
    {M N : Type*} [CommGroup M] [CommGroup N] [IsMulTorsionFree N]
    (f : M →* N) (m : M) :
    torsionFreeFactor f (QuotientGroup.mk m) = f m := by
  rfl

/-- The torsion-free quotient of a finitely generated character group is a
finite free integer module, hence the character group of a split torus. -/
theorem torsionFreeCharacterModule_free
    (M : Type u) [CommGroup M] [Group.FG M] :
    Module.Free ℤ (Additive (M ⧸ CommGroup.torsion M)) := by
  let : AddGroup.FG (Additive (M ⧸ CommGroup.torsion M)) := by
    exact AddGroup.fg_iff_mul_fg.mpr inferInstance
  have : Module.Finite ℤ (Additive (M ⧸ CommGroup.torsion M)) :=
    Module.Finite.iff_addGroup_fg.mpr this
  exact Module.free_of_finite_type_torsion_free'

/-- A finitely generated character group modulo torsion is (noncanonically)
the character lattice of a finite-rank split torus. -/
theorem TorsionFreeCharacterGroup.exists_finLattice
    (M : Type u) [CommGroup M] [Group.FG M] :
    ∃ r : ℕ, Nonempty
      ((M ⧸ CommGroup.torsion M) ≃* Multiplicative (Fin r →₀ ℤ)) := by
  have hfinite : Module.Finite ℤ (Additive (M ⧸ CommGroup.torsion M)) :=
    Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr inferInstance)
  obtain ⟨r, b⟩ :=
    Module.basisOfFiniteTypeTorsionFree' (R := ℤ)
      (M := Additive (M ⧸ CommGroup.torsion M))
  exact ⟨r, ⟨(MulEquiv.multiplicativeAdditive
    (M ⧸ CommGroup.torsion M)).symm.trans
      (AddEquiv.toMultiplicative b.repr.toAddEquiv)⟩⟩

end ReductiveGroups
