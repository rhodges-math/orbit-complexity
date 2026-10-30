import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientRootSpaces
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRootDerived
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Center Quotient Weight Descent

Descend adjoint weights through the original Lie algebra's center
quotient, with an arbitrary choice of the original Lie algebra is semisimple. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieModule

variable {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

omit [IsAlgClosed K] in
private theorem CenterQuotientCartanMap.ker_le_weight_ker
    (χ : Weight K H L) :
    (centerQuotientCartanMap H).toLinearMap.ker ≤ χ.toLinear.ker := by
  intro h hh
  have hh0 : centerQuotientLieHom (K := K) (h : L) = 0 := by
    have hh' : centerQuotientCartanMap H h = 0 := hh
    exact congrArg Subtype.val hh'
  have hcenter : (h : L) ∈ center K L := by
    rw [← centerQuotientLieHom_ker]
    exact hh0
  change χ h = 0
  exact rootWeight_apply_eq_zero_of_mem_center H χ h hcenter

/-- The adjoint weight functional on the original Cartan subalgebra,
factored through its image in the center quotient. -/
def centerQuotientWeightDescent (χ : Weight K H L) :
    centerQuotientCartan H →ₗ[K] K :=
  let f := (centerQuotientCartanMap H).toLinearMap
  (f.ker.liftQ χ.toLinear (CenterQuotientCartanMap.ker_le_weight_ker H χ)).comp
    (f.quotKerEquivOfSurjective (centerQuotientCartanMap_surjective H)).symm.toLinearMap

omit [IsAlgClosed K] in
/-- The equality is

```lean
centerQuotientWeightDescent H χ (centerQuotientCartanMap H h) = χ h
```
-/
@[simp] theorem centerQuotientWeightDescent_apply_map
    (χ : Weight K H L) (h : H) :
    centerQuotientWeightDescent H χ (centerQuotientCartanMap H h) = χ h := by
  let f := (centerQuotientCartanMap H).toLinearMap
  change (f.ker.liftQ χ.toLinear (CenterQuotientCartanMap.ker_le_weight_ker H χ))
    ((f.quotKerEquivOfSurjective (centerQuotientCartanMap_surjective H)).symm (f h)) = χ h
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

omit [IsAlgClosed K] in
/-- A nonzero original adjoint weight remains nonzero after descent. -/
theorem centerQuotientWeightDescent_ne_zero
    (χ : Weight K H L) (hχ : ¬ χ.IsZero) :
    centerQuotientWeightDescent H χ ≠ 0 := by
  intro hz
  apply hχ
  apply funext
  intro h
  have hh := congrArg (fun f : centerQuotientCartan H →ₗ[K] K =>
    f (centerQuotientCartanMap H h)) hz
  change χ h = 0
  simpa only [centerQuotientWeightDescent_apply_map, LinearMap.zero_apply] using hh

/-- Each nonzero occurring adjoint weight on the original Cartan descends to
an occurring weight of the center quotient. -/
def centerQuotientWeightOfNonZero
    (χ : Weight K H L) (hχ : ¬ χ.IsZero) :
    Weight K (centerQuotientCartan H) (L ⧸ LieAlgebra.center K L) := by
  classical
  let ψ := centerQuotientWeightDescent H χ
  have hψ : (ψ : centerQuotientCartan H → K) ≠ 0 := by
    intro hz
    exact (centerQuotientWeightDescent_ne_zero H χ hχ)
      (DFunLike.coe_injective hz)
  have hcomp : (fun h : H => ψ (centerQuotientCartanMap H h)) = (χ : H → K) := by
    funext h
    exact centerQuotientWeightDescent_apply_map H χ h
  let x := Classical.choose χ.exists_ne_zero
  have hx := (Classical.choose_spec χ.exists_ne_zero).1
  have hx0 := (Classical.choose_spec χ.exists_ne_zero).2
  have hx' : x ∈ rootSpace H (fun h => ψ (centerQuotientCartanMap H h)) := by
    rw [hcomp]
    exact hx
  let x' : rootSpace H (fun h => ψ (centerQuotientCartanMap H h)) := ⟨x, hx'⟩
  let y := centerQuotientRootSpaceEquiv H (ψ : centerQuotientCartan H → K) hψ x'
  have hy : y ≠ 0 := by
    intro hz
    have hxzero : x' = 0 :=
      (centerQuotientRootSpaceEquiv H (ψ : centerQuotientCartan H → K) hψ).injective
        (by simpa only [map_zero] using hz)
    exact hx0 (congrArg Subtype.val hxzero)
  refine ⟨ψ, ?_⟩
  intro hbot
  have hyzero : (y : L ⧸ LieAlgebra.center K L) = 0 :=
    (LieSubmodule.eq_bot_iff (N := rootSpace (centerQuotientCartan H)
      (ψ : centerQuotientCartan H → K))).mp hbot y y.property
  exact hy (Subtype.ext hyzero)

/-- The equality is

```lean
centerQuotientWeightOfNonZero H χ hχ (centerQuotientCartanMap H h) = χ h
```
-/
@[simp] theorem centerQuotientWeightOfNonZero_apply_map
    (χ : Weight K H L) (hχ : ¬ χ.IsZero) (h : H) :
    centerQuotientWeightOfNonZero H χ hχ (centerQuotientCartanMap H h) = χ h := by
  exact centerQuotientWeightDescent_apply_map H χ h

/-- Every nonzero occurring quotient weight pulls back to an occurring weight
on the original Cartan. Its nonzero root space is lifted by the
center-quotient root-space equivalence. -/
def originalWeightOfCenterQuotientNonZero
    (ψ : Weight K (centerQuotientCartan H) (L ⧸ LieAlgebra.center K L))
    (hψ : ψ.IsNonZero) : Weight K H L := by
  classical
  let f : H → K := fun h => ψ (centerQuotientCartanMap H h)
  have hψne : (ψ : centerQuotientCartan H → K) ≠ 0 := hψ
  let e := centerQuotientRootSpaceEquiv H (ψ : centerQuotientCartan H → K) hψne
  let y := Classical.choose ψ.exists_ne_zero
  have hy := (Classical.choose_spec ψ.exists_ne_zero).1
  have hy0 := (Classical.choose_spec ψ.exists_ne_zero).2
  let x := e.symm (⟨y, hy⟩ : rootSpace (centerQuotientCartan H) (ψ : _ → K))
  have hx0 : x ≠ 0 := by
    intro hx
    have hy' : (⟨y, hy⟩ : rootSpace (centerQuotientCartan H) (ψ : _ → K)) = 0 := by
      have := congrArg e hx
      change e (e.symm (⟨y, hy⟩ : rootSpace (centerQuotientCartan H) (ψ : _ → K))) =
        e 0 at this
      simpa only [map_zero, LinearEquiv.apply_symm_apply] using this
    exact hy0 (congrArg Subtype.val hy')
  refine ⟨f, ?_⟩
  intro hbot
  have hx : (x : L) = 0 :=
    (LieSubmodule.eq_bot_iff (N := rootSpace H f)).mp hbot x x.property
  exact hx0 (Subtype.ext hx)

omit [CharZero K] in
/-- The equality is

```lean
originalWeightOfCenterQuotientNonZero H ψ hψ h =
      ψ (centerQuotientCartanMap H h)
```
-/
@[simp] theorem OriginalWeightOfCenterQuotientNonZero.apply
    (ψ : Weight K (centerQuotientCartan H) (L ⧸ LieAlgebra.center K L))
    (hψ : ψ.IsNonZero) (h : H) :
    originalWeightOfCenterQuotientNonZero H ψ hψ h =
      ψ (centerQuotientCartanMap H h) := rfl

/-- Nonzero occurring weights of the original adjoint representation and
its center quotient have equivalent indices. -/
def nonzeroCenterQuotientWeightEquiv :
    {χ : Weight K H L // χ.IsNonZero} ≃
      {ψ : Weight K (centerQuotientCartan H) (L ⧸ LieAlgebra.center K L) //
        ψ.IsNonZero} := by
  let F : {χ : Weight K H L // χ.IsNonZero} →
      {ψ : Weight K (centerQuotientCartan H) (L ⧸ LieAlgebra.center K L) //
        ψ.IsNonZero} := fun χ =>
    ⟨centerQuotientWeightOfNonZero H χ χ.property, by
      change (centerQuotientWeightDescent H χ : centerQuotientCartan H → K) ≠ 0
      exact DFunLike.coe_injective.mt (centerQuotientWeightDescent_ne_zero H χ χ.property)⟩
  apply Equiv.ofBijective F
  constructor
  · intro χ θ h
    apply Subtype.ext
    apply Weight.ext
    intro x
    have hh := congrArg (fun ψ : Weight K (centerQuotientCartan H)
      (L ⧸ LieAlgebra.center K L) => ψ (centerQuotientCartanMap H x))
      (congrArg Subtype.val h)
    simpa only [F, centerQuotientWeightOfNonZero_apply_map] using hh
  · intro ψ
    let χ := originalWeightOfCenterQuotientNonZero H ψ ψ.property
    have hχ : χ.IsNonZero := by
      intro hz
      apply ψ.property
      apply funext
      intro y
      obtain ⟨x, rfl⟩ := centerQuotientCartanMap_surjective H y
      have hh := congrFun hz x
      change originalWeightOfCenterQuotientNonZero H ψ ψ.property x = 0 at hh
      rw [OriginalWeightOfCenterQuotientNonZero.apply] at hh
      exact hh
    refine ⟨⟨χ, hχ⟩, ?_⟩
    apply Subtype.ext
    apply Weight.ext
    intro y
    obtain ⟨x, rfl⟩ := centerQuotientCartanMap_surjective H y
    change centerQuotientWeightOfNonZero H χ hχ
      (centerQuotientCartanMap H x) = ψ.val (centerQuotientCartanMap H x)
    rw [centerQuotientWeightOfNonZero_apply_map]
    exact OriginalWeightOfCenterQuotientNonZero.apply H ψ ψ.property x

/-- The equality is

```lean
(nonzeroCenterQuotientWeightEquiv H χ).val (centerQuotientCartanMap H h) =
      χ.val h
```
-/
@[simp] theorem NonzeroCenterQuotientWeightEquiv.apply_map
    (χ : {χ : Weight K H L // χ.IsNonZero}) (h : H) :
    (nonzeroCenterQuotientWeightEquiv H χ).val (centerQuotientCartanMap H h) =
      χ.val h := by
  exact centerQuotientWeightOfNonZero_apply_map H χ.val χ.property h

end ReductiveGroups
