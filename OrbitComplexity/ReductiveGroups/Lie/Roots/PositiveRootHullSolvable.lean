import OrbitComplexity.ReductiveGroups.Lie.Roots.PositiveRootHeightBracket
import OrbitComplexity.ReductiveGroups.Lie.Roots.FinitePositiveGradingSolvable

/-!
# Positive Root Hull Solvable

The positive root-space Lie algebra is solvable. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

private def positiveRootLieSubmodule : LieSubmodule K H L :=
  ⨆ (α : H.root) (_ : b.IsPos α), rootSpace H α.val

private theorem positiveRootLieSubmodule_lie_mem
    (x y : L) (hx : x ∈ positiveRootLieSubmodule H b)
    (hy : y ∈ positiveRootLieSubmodule H b) :
    ⁅x, y⁆ ∈ positiveRootLieSubmodule H b := by
  let N := positiveRootLieSubmodule H b
  have hpair (α β : H.root) (hα : b.IsPos α) (hβ : b.IsPos β)
      (x y : L) (hx : x ∈ rootSpace H α.val) (hy : y ∈ rootSpace H β.val) :
      ⁅x, y⁆ ∈ N := by
    have hsum := positive_root_bracket_mem_sum_height H b α β hα hβ x y hx hy
    have hle : (⨆ (γ : H.root)
        (_ : b.height γ = b.height α + b.height β), rootSpace H γ.val) ≤ N := by
      refine iSup₂_le fun γ hγ => ?_
      have hγpos : b.IsPos γ := by
        change 0 < b.height γ
        change 0 < b.height α at hα
        change 0 < b.height β at hβ
        omega
      exact le_iSup₂_of_le γ hγpos le_rfl
    exact hle hsum
  change x ∈ ⨆ (α : H.root) (_ : b.IsPos α), rootSpace H α.val at hx
  suffices hh : ∀ x ∈ ⨆ (α : H.root) (_ : b.IsPos α), rootSpace H α.val,
      ∀ y ∈ N, ⁅x, y⁆ ∈ N from hh x hx y hy
  intro x hx
  refine LieSubmodule.iSup_induction
    (motive := fun x => ∀ y ∈ N, ⁅x, y⁆ ∈ N) _ hx ?_ ?_ ?_
  · intro α x hαx
    refine LieSubmodule.iSup_induction
      (motive := fun x => ∀ y ∈ N, ⁅x, y⁆ ∈ N) _ hαx ?_ ?_ ?_
    · intro hα x hx y hy
      change y ∈ ⨆ (β : H.root) (_ : b.IsPos β), rootSpace H β.val at hy
      refine LieSubmodule.iSup_induction
        (motive := fun y => ⁅x, y⁆ ∈ N) _ hy ?_ ?_ ?_
      · intro β y hβy
        refine LieSubmodule.iSup_induction
          (motive := fun y => ⁅x, y⁆ ∈ N) _ hβy ?_ ?_ ?_
        · intro hβ y hy
          exact hpair α β hα hβ x y hx hy
        · simp
        · intro y₁ y₂ hy₁ hy₂
          simpa only [lie_add] using add_mem hy₁ hy₂
      · simp
      · intro y₁ y₂ hy₁ hy₂
        simpa only [lie_add] using add_mem hy₁ hy₂
    · simp
    · intro x₁ x₂ hx₁ hx₂ y hy
      simpa only [add_lie] using add_mem (hx₁ y hy) (hx₂ y hy)
  · simp
  · intro x₁ x₂ hx₁ hx₂ y hy
    simpa only [add_lie] using add_mem (hx₁ y hy) (hx₂ y hy)

/-- The sum of the positive root spaces is a Lie subalgebra. -/
def positiveRootLieSubalgebra : LieSubalgebra K L :=
  { (positiveRootLieSubmodule H b).toSubmodule with
    lie_mem' := by
      intro x y hx hy
      exact positiveRootLieSubmodule_lie_mem H b x y hx hy }

private abbrev PositiveRootIndex := {α : H.root // b.IsPos α}

private def positiveRootComponent (α : PositiveRootIndex H b) :
    Submodule K (positiveRootLieSubalgebra H b) :=
  (rootSpace H α.val.val).toSubmodule.comap
    (positiveRootLieSubalgebra H b).incl.toLinearMap

private theorem positiveRootComponent_iSup_eq_top :
    (⨆ α : PositiveRootIndex H b, positiveRootComponent H b α) = ⊤ := by
  let s : Set H.root := {α | b.IsPos α}
  let p : H.root → Submodule K L := fun α => (rootSpace H α.val).toSubmodule
  let N := positiveRootLieSubalgebra H b
  let f : N →ₗ[K] L := N.incl.toLinearMap
  have hf : Function.Injective f := Subtype.coe_injective
  apply (Submodule.map_injective_of_injective hf)
  rw [Submodule.map_iSup, Submodule.map_top]
  have hcarrier : (N : Submodule K L) = ⨆ i ∈ s, p i := by
    simp [N, s, p, positiveRootLieSubalgebra,
      positiveRootLieSubmodule, LieSubmodule.iSup_toSubmodule]
  have hrange : LinearMap.range f = (N : Submodule K L) := by
    exact (N : Submodule K L).range_subtype
  rw [hrange, hcarrier]
  simp only [positiveRootComponent]
  have hmap (α : PositiveRootIndex H b) :
      Submodule.map f (Submodule.comap
        (positiveRootLieSubalgebra H b).incl.toLinearMap
        (rootSpace H α.val.val).toSubmodule) = p α.val := by
    change Submodule.map f (Submodule.comap f (p α.val)) = p α.val
    rw [Submodule.map_comap_eq, hrange, inf_eq_right]
    rw [hcarrier]
    exact le_iSup₂_of_le α.val α.property le_rfl
  simp_rw [hmap]
  exact iSup_subtype'' s p

/-- The Lie algebra spanned by the positive root spaces of a Cartan
root system is solvable. -/
theorem positiveRootLieSubalgebra_isSolvable :
    LieAlgebra.IsSolvable (positiveRootLieSubalgebra H b) := by
  classical
  let N := positiveRootLieSubalgebra H b
  let V : PositiveRootIndex H b → Submodule K N := positiveRootComponent H b
  let degree : PositiveRootIndex H b → ℕ := fun α => (b.height α.val).toNat
  have htop : (⨆ α, V α) = ⊤ := positiveRootComponent_iSup_eq_top H b
  have hpos (α : PositiveRootIndex H b) : 0 < degree α := by
    change 0 < (b.height α.val).toNat
    have hα : 0 < b.height α.val := α.property
    omega
  have hbracket (α β : PositiveRootIndex H b) (x y : N)
      (hx : x ∈ V α) (hy : y ∈ V β) :
      ⁅x, y⁆ ∈ positiveGradingAbove V degree (degree α + degree β) := by
    let q := positiveGradingAbove V degree (degree α + degree β)
    let f : N →ₗ[K] L := N.incl.toLinearMap
    have hx' : (x : L) ∈ rootSpace H α.val.val := hx
    have hy' : (y : L) ∈ rootSpace H β.val.val := hy
    have hsum := positive_root_bracket_mem_sum_height H b α.val β.val
      α.property β.property (x : L) (y : L) hx' hy'
    have hrange : LinearMap.range f = (N : Submodule K L) :=
      (N : Submodule K L).range_subtype
    have hle : (⨆ (γ : H.root)
        (_ : b.height γ = b.height α.val + b.height β.val),
        (rootSpace H γ.val).toSubmodule) ≤ q.map f := by
      refine iSup₂_le fun γ hγ => ?_
      have hγpos : b.IsPos γ := by
        change 0 < b.height γ
        have hα := α.property
        have hβ := β.property
        change 0 < b.height α.val at hα
        change 0 < b.height β.val at hβ
        omega
      let γ' : PositiveRootIndex H b := ⟨γ, hγpos⟩
      have hdegree : degree α + degree β ≤ degree γ' := by
        change (b.height α.val).toNat + (b.height β.val).toNat ≤
          (b.height γ).toNat
        have hα := α.property
        have hβ := β.property
        change 0 < b.height α.val at hα
        change 0 < b.height β.val at hβ
        omega
      have hrootN : (rootSpace H γ.val).toSubmodule ≤ (N : Submodule K L) := by
        have hrootN' : rootSpace H γ.val ≤ positiveRootLieSubmodule H b :=
          le_iSup₂_of_le γ hγpos le_rfl
        intro z hz
        exact hrootN' hz
      have hmap : Submodule.map f (V γ') = (rootSpace H γ.val).toSubmodule := by
        change Submodule.map f (Submodule.comap f
          (rootSpace H γ.val).toSubmodule) = _
        rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hrootN]
      rw [← hmap]
      exact Submodule.map_mono (le_iSup₂_of_le γ' hdegree le_rfl)
    have hsum' : ⁅(x : L), (y : L)⁆ ∈
        ⨆ (γ : H.root)
          (_ : b.height γ = b.height α.val + b.height β.val),
          (rootSpace H γ.val).toSubmodule := by
      have heq :
          ((⨆ (γ : H.root)
            (_ : b.height γ = b.height α.val + b.height β.val),
            rootSpace H γ.val) : LieSubmodule K H L).toSubmodule =
          ⨆ (γ : H.root)
            (_ : b.height γ = b.height α.val + b.height β.val),
            (rootSpace H γ.val).toSubmodule := by
        simp only [LieSubmodule.iSup_toSubmodule]
      rw [← heq]
      exact hsum
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp (hle hsum')
    have hzeq : z = ⁅x, y⁆ := by
      apply Subtype.ext
      simpa [f] using hzx
    exact hzeq ▸ hz
  let : Fintype (PositiveRootIndex H b) := Fintype.ofFinite _
  let bound := (Finset.univ.sup degree) + 1
  have hbound (α : PositiveRootIndex H b) : degree α < bound := by
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ α))
  exact isSolvable_of_finite_positive_grading V degree htop hpos
    (fun α β x y hx hy => hbracket α β x y hx hy) bound hbound

/-- The Cartan together with all positive root spaces, as a Lie
subalgebra with exactly the expected linear carrier. -/
def cartanPositiveRootHull : LieSubalgebra K L :=
  { H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule with
    lie_mem' := by
      intro x y hx hy
      obtain ⟨xh, hxh, xp, hxp, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨yh, hyh, yp, hyp, rfl⟩ := Submodule.mem_sup.mp hy
      have hhh : ⁅xh, yh⁆ ∈ H.toSubmodule := H.lie_mem hxh hyh
      have hhp : ⁅xh, yp⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
        simpa [positiveRootLieSubalgebra] using
          (positiveRootLieSubmodule H b).lie_mem (x := (⟨xh, hxh⟩ : H)) hyp
      have hph : ⁅xp, yh⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
        have hh : ⁅yh, xp⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
          simpa [positiveRootLieSubalgebra] using
            (positiveRootLieSubmodule H b).lie_mem (x := (⟨yh, hyh⟩ : H)) hxp
        rw [← lie_skew]
        exact neg_mem hh
      have hpp : ⁅xp, yp⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule :=
        (positiveRootLieSubalgebra H b).lie_mem hxp hyp
      have h₁ : ⁅xh, yh⁆ ∈ H.toSubmodule ⊔
          (positiveRootLieSubalgebra H b).toSubmodule :=
        (le_sup_left : H.toSubmodule ≤
          H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule) hhh
      have h₂ : ⁅xh, yp⁆ ∈ H.toSubmodule ⊔
          (positiveRootLieSubalgebra H b).toSubmodule :=
        (le_sup_right : (positiveRootLieSubalgebra H b).toSubmodule ≤
          H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule) hhp
      have h₃ : ⁅xp, yh⁆ ∈ H.toSubmodule ⊔
          (positiveRootLieSubalgebra H b).toSubmodule :=
        (le_sup_right : (positiveRootLieSubalgebra H b).toSubmodule ≤
          H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule) hph
      have h₄ : ⁅xp, yp⁆ ∈ H.toSubmodule ⊔
          (positiveRootLieSubalgebra H b).toSubmodule :=
        (le_sup_right : (positiveRootLieSubalgebra H b).toSubmodule ≤
          H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule) hpp
      change ⁅xh + xp, yh + yp⁆ ∈ H.toSubmodule ⊔
        (positiveRootLieSubalgebra H b).toSubmodule
      simpa only [add_lie, lie_add, add_assoc, add_left_comm, add_comm] using
        add_mem (add_mem h₁ h₂) (add_mem h₃ h₄) }

/-- The equality is

```lean
(cartanPositiveRootHull H b).toSubmodule =
      H.toSubmodule ⊔
        (⨆ (α : H.root) (_ : b.IsPos α),
          (rootSpace H α.val).toSubmodule)
```
-/
theorem cartanPositiveRootHull_carrier :
    (cartanPositiveRootHull H b).toSubmodule =
      H.toSubmodule ⊔
        (⨆ (α : H.root) (_ : b.IsPos α),
          (rootSpace H α.val).toSubmodule) := by
  simp only [cartanPositiveRootHull, positiveRootLieSubalgebra,
    positiveRootLieSubmodule, LieSubmodule.iSup_toSubmodule]

/-- The inclusion is

```lean
H ≤ cartanPositiveRootHull H b
```
-/
theorem cartan_le_cartanPositiveRootHull : H ≤ cartanPositiveRootHull H b := by
  intro x hx
  exact (le_sup_left : H.toSubmodule ≤
    H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule) hx

private def positiveRootIdeal : LieIdeal K (cartanPositiveRootHull H b) :=
  { (positiveRootLieSubalgebra H b).toSubmodule.comap
      (cartanPositiveRootHull H b).incl.toLinearMap with
    lie_mem := by
      intro x y hy
      change ⁅(x : L), (y : L)⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule
      have hx : (x : L) ∈ H.toSubmodule ⊔
          (positiveRootLieSubalgebra H b).toSubmodule := x.property
      obtain ⟨xh, hxh, xp, hxp, hsum⟩ := Submodule.mem_sup.mp hx
      have hh : ⁅xh, (y : L)⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
        simpa [positiveRootLieSubalgebra] using
          (positiveRootLieSubmodule H b).lie_mem (x := (⟨xh, hxh⟩ : H)) hy
      have hp : ⁅xp, (y : L)⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule :=
        (positiveRootLieSubalgebra H b).lie_mem hxp hy
      rw [← hsum, add_lie]
      exact add_mem hh hp }

private def positiveRootIdealInclusion :
    positiveRootIdeal H b →ₗ⁅K⁆ positiveRootLieSubalgebra H b where
  toLinearMap :=
    { toFun := fun z => ⟨((z : cartanPositiveRootHull H b) : L), z.property⟩
      map_add' := fun x y => by apply Subtype.ext; rfl
      map_smul' := fun c x => by apply Subtype.ext; rfl }
  map_lie' := by intro x y; apply Subtype.ext; rfl

private theorem positiveRootIdeal_isSolvable :
    LieAlgebra.IsSolvable (positiveRootIdeal H b) := by
  let _ : LieAlgebra.IsSolvable (positiveRootLieSubalgebra H b) :=
    positiveRootLieSubalgebra_isSolvable H b
  have hinj : Function.Injective (positiveRootIdealInclusion H b) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : positiveRootLieSubalgebra H b => (z : L)) hxy
  exact hinj.lieAlgebra_isSolvable

private theorem CartanPositiveRootHull.bracket_mem_positiveRootIdeal
    (x y : cartanPositiveRootHull H b) :
    ⁅x, y⁆ ∈ positiveRootIdeal H b := by
  have hx : (x : L) ∈ H.toSubmodule ⊔
      (positiveRootLieSubalgebra H b).toSubmodule := x.property
  have hy : (y : L) ∈ H.toSubmodule ⊔
      (positiveRootLieSubalgebra H b).toSubmodule := y.property
  obtain ⟨xh, hxh, xp, hxp, hxeq⟩ := Submodule.mem_sup.mp hx
  obtain ⟨yh, hyh, yp, hyp, hyeq⟩ := Submodule.mem_sup.mp hy
  have hhh : ⁅xh, yh⁆ = 0 := by
    have hab : ⁅(⟨xh, hxh⟩ : H), (⟨yh, hyh⟩ : H)⁆ = 0 :=
      (inferInstance : LieModule.IsTrivial H H).trivial _ _
    simpa [LieSubalgebra.coe_bracket] using
      congrArg (fun z : H => (z : L)) hab
  have hhp : ⁅xh, yp⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
    simpa [positiveRootLieSubalgebra] using
      (positiveRootLieSubmodule H b).lie_mem (x := (⟨xh, hxh⟩ : H)) hyp
  have hph : ⁅xp, yh⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
    have hh : ⁅yh, xp⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule := by
      simpa [positiveRootLieSubalgebra] using
        (positiveRootLieSubmodule H b).lie_mem (x := (⟨yh, hyh⟩ : H)) hxp
    rw [← lie_skew]
    exact neg_mem hh
  have hpp : ⁅xp, yp⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule :=
    (positiveRootLieSubalgebra H b).lie_mem hxp hyp
  change ⁅(x : L), (y : L)⁆ ∈ (positiveRootLieSubalgebra H b).toSubmodule
  rw [← hxeq, ← hyeq, add_lie, lie_add, lie_add, hhh, zero_add]
  exact add_mem hhp (add_mem hph hpp)

/-- The Cartan plus all positive root spaces is solvable. The first
derived ideal lies in the positive-root ideal, whose finite height grading
terminates its derived series. -/
theorem cartanPositiveRootHull_isSolvable :
    LieAlgebra.IsSolvable (cartanPositiveRootHull H b) := by
  let B := cartanPositiveRootHull H b
  let I := positiveRootIdeal H b
  let _ : LieAlgebra.IsSolvable I := positiveRootIdeal_isSolvable H b
  have hfirst : LieAlgebra.derivedSeries K B 1 ≤ I := by
    rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
      LieAlgebra.derivedSeriesOfIdeal_zero, LieSubmodule.lie_le_iff]
    intro x hx y hy
    exact CartanPositiveRootHull.bracket_mem_positiveRootIdeal H b x y
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K I
  have hkI : LieAlgebra.derivedSeriesOfIdeal K B k I = ⊥ :=
    (I.derivedSeries_eq_bot_iff k).mp hk
  apply LieAlgebra.IsSolvable.mk (R := K)
  apply eq_bot_iff.mpr
  calc
    LieAlgebra.derivedSeries K B (k + 1) =
        LieAlgebra.derivedSeriesOfIdeal K B k (LieAlgebra.derivedSeries K B 1) := by
          rw [LieAlgebra.derivedSeries_def,
            ← LieAlgebra.derivedSeriesOfIdeal_add]
    _ ≤ LieAlgebra.derivedSeriesOfIdeal K B k I :=
      LieAlgebra.derivedSeriesOfIdeal_mono hfirst k
    _ = ⊥ := hkI

end ReductiveGroups
