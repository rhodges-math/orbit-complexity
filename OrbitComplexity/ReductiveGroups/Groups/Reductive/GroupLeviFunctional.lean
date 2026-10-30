import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# A central torus point for the selected Levi roots

Prescribing simple-root character values constructs a torus point whose root
values are integral powers of two. Its exponent is the omitted-coordinate sum.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The integral functional vanishing on selected simples and taking value one on the others. -/
def leviFunctional (I : Set G.rootBase.support) : G.rootSystem.rootSpan ℤ →ₗ[ℤ] ℤ := by
  classical
  exact G.rootBase.toWeightBasisInt.constr ℤ (fun i => if i ∈ I then 0 else 1)

/-- A central torus point evaluates each root character as two to its omitted-coordinate sum. -/
theorem exists_leviFunctional_point (I : Set G.rootBase.support) :
    ∃ z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K),
      (∀ i ∈ I, z.ofConv (MonoidAlgebra.single (G.rootCharacter i.val) 1) = 1) ∧
      ∀ r : G.rootIndex, z.ofConv (MonoidAlgebra.single (G.rootCharacter r) 1) =
        (2 : K) ^ (G.leviFunctional I (G.rootSystem.rootSpanMem ℤ r)) := by
  classical
  let two : Kˣ := Units.mk0 2 two_ne_zero
  let c : G.rootBase.support → Kˣ := fun i => two ^ (if i ∈ I then (0 : ℤ) else 1)
  obtain ⟨z, hz⟩ := exists_torusPoint_character_values (K := K)
    (fun i : G.rootBase.support => G.rootCharacter i.val) G.rootCharacter_independent c
  refine ⟨z, ?_, ?_⟩
  · intro i hi
    simpa only [c, ite_eq_left hi, zpow_zero, Units.val_one] using hz i
  · let e : G.characters →* K := z.ofConv.toMonoidHom.comp (MonoidAlgebra.of K _)
    let p : G.rootSystem.rootSpan ℤ →ₗ[ℤ] Additive Kˣ :=
      e.toHomUnits.toAdditive.toIntLinearMap.comp G.rootCharacterMap
    let q : G.rootSystem.rootSpan ℤ →ₗ[ℤ] Additive Kˣ :=
      G.rootBase.toWeightBasisInt.constr ℤ (fun i => Additive.ofMul (c i))
    have hpq : p = q := by
      apply G.rootBase.toWeightBasisInt.ext
      intro i
      rw [show q (G.rootBase.toWeightBasisInt i) = Additive.ofMul (c i) from
        G.rootBase.toWeightBasisInt.constr_basis ℤ _ i]
      apply Additive.toMul.injective
      apply Units.ext
      change e (Multiplicative.ofAdd
        (G.rootCharacterMap (G.rootBase.toWeightBasisInt i))) = c i
      rw [rootCharacterMap, Module.Basis.constr_basis]
      exact hz i
    let zp : ℤ →+ Additive Kˣ :=
      { toFun := fun n => Additive.ofMul (two ^ n)
        map_zero' := by simp
        map_add' := by intro a b; exact zpow_add two a b }
    have hq : q = zp.toIntLinearMap.comp (G.leviFunctional I) := by
      apply G.rootBase.toWeightBasisInt.ext
      intro i
      simp only [q, leviFunctional, LinearMap.comp_apply, Module.Basis.constr_basis]
      rfl
    intro r
    have h := congrArg (fun t : Additive Kˣ => ((Additive.toMul t : Kˣ) : K))
      (LinearMap.congr_fun (hpq.trans hq) (G.rootSystem.rootSpanMem ℤ r))
    change e (Multiplicative.ofAdd (G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ r))) =
      ((two ^ (G.leviFunctional I (G.rootSystem.rootSpanMem ℤ r)) : Kˣ) : K) at h
    rw [G.rootCharacterMap_root] at h
    change z.ofConv (MonoidAlgebra.single (G.rootCharacter r) 1) =
      ((two ^ (G.leviFunctional I (G.rootSystem.rootSpanMem ℤ r)) : Kˣ) : K) at h
    simpa only [two, Units.val_zpow_eq_zpow_val, Units.val_mk0] using h

end ReductiveGroups.ReductiveGroupData
