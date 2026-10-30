import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRootDerived
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalQuotient

/-!
# Root Space Center Quotient

Passing to the center quotient loses no vector in a nonzero
root space of the original Lie algebra. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]

/-- The equality is

```lean
x = 0
```
-/
theorem rootSpace_mem_center_eq_zero
    (χ : H → K) (hχ : χ ≠ 0) (x : L)
    (hx : x ∈ rootSpace H χ) (hc : x ∈ center K L) : x = 0 := by
  obtain ⟨h, hh⟩ : ∃ h : H, χ h ≠ 0 := by
    by_contra hn
    apply hχ
    funext h
    simpa using (not_exists.mp hn h)
  let F : Module.End K L := toEnd K H L h - χ h • 1
  have hF : F x = (-χ h) • x := by
    change ⁅(h : L), x⁆ - χ h • x = (-χ h) • x
    rw [hc (h : L), zero_sub, neg_smul]
  have hpow (k : ℕ) : (F ^ k) x = (-χ h) ^ k • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hF, smul_smul]
      rw [pow_succ]
  obtain ⟨k, hk⟩ := (mem_genWeightSpace L χ x).mp hx h
  change (F ^ k) x = 0 at hk
  rw [hpow] at hk
  exact (smul_eq_zero.mp hk).resolve_left (pow_ne_zero k (neg_ne_zero.mpr hh))

/-- The quotient projection is injective on each nonzero original
root space. -/
theorem centerQuotient_injective_on_rootSpace
    (χ : H → K) (hχ : χ ≠ 0) :
    Function.Injective (fun x : rootSpace H χ =>
      centerQuotientLieHom (K := K) (x : L)) := by
  intro x y hxy
  dsimp only at hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply rootSpace_mem_center_eq_zero H χ hχ
    ((x : L) - (y : L)) ((rootSpace H χ).sub_mem x.property y.property)
  have hz : centerQuotientLieHom (K := K) ((x : L) - (y : L)) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact (LieSubmodule.Quotient.mk_eq_zero (N := center K L)).mp hz

/-- The equality is

```lean
centerQuotientLieHom (K := K) (x : L) ≠ 0
```
-/
theorem centerQuotient_rootSpace_ne_zero
    (χ : H → K) (hχ : χ ≠ 0) (x : rootSpace H χ) (hx : x ≠ 0) :
    centerQuotientLieHom (K := K) (x : L) ≠ 0 := by
  intro hz
  apply hx
  apply centerQuotient_injective_on_rootSpace H χ hχ
  simpa only [ZeroMemClass.coe_zero, map_zero] using hz

end ReductiveGroups
