import OrbitComplexity.ReductiveGroups.Lie.Cartan.KillingPerfect
import Mathlib.Algebra.Lie.Extension

/-!
# Split Central Derived

The derived algebra of a split central extension of a perfect Killing Lie algebra. -/

noncomputable section
namespace ReductiveGroups

variable {K N S : Type*} [Field K] [LieRing N] [LieAlgebra K N]
  [LieRing S] [LieAlgebra K S] [Module.Finite K S]
  [LieAlgebra.IsKilling K S]

/-- In a central extension, a Lie section identifies the original Killing algebra
with the derived algebra of the extension. -/
noncomputable def centralExtensionDerivedLieEquiv
    (E : LieAlgebra.Extension K N S)
    (hc : ∀ (x : E.L) (n : N), ⁅x, E.incl n⁆ = 0)
    (t : S →ₗ⁅K⁆ E.L)
    (ht : ∀ s : S, E.proj (t s) = s) :
    S ≃ₗ⁅K⁆ LieAlgebra.derivedSeries K E.L 1 := by
  have hker_central (u : E.L) (hu : E.proj u = 0) (v : E.L) : ⁅v, u⁆ = 0 := by
    have hm : u ∈ E.incl.range := by
      rw [E.IsExtension.exact]
      exact LieHom.mem_ker.mpr hu
    obtain ⟨n, hn⟩ := hm
    rw [← hn]
    exact hc v n
  have hker_central_left (u : E.L) (hu : E.proj u = 0) (v : E.L) : ⁅u, v⁆ = 0 := by
    rw [← lie_skew u v, hker_central u hu v, neg_zero]
  have hdiff (x : E.L) : E.proj (x - t (E.proj x)) = 0 := by
    simp [ht]
  have hdecomp (x : E.L) : x = t (E.proj x) + (x - t (E.proj x)) := by
    abel
  have hbr (x y : E.L) : ⁅x, y⁆ = t ⁅E.proj x, E.proj y⁆ := by
    calc
      ⁅x, y⁆ = ⁅t (E.proj x) + (x - t (E.proj x)), y⁆ := by rw [← hdecomp x]
      _ = ⁅t (E.proj x), y⁆ := by rw [add_lie, hker_central_left _ (hdiff x) y, add_zero]
      _ = ⁅t (E.proj x), t (E.proj y) + (y - t (E.proj y))⁆ := by rw [← hdecomp y]
      _ = ⁅t (E.proj x), t (E.proj y)⁆ := by rw [lie_add, hker_central _ (hdiff y) _, add_zero]
      _ = t ⁅E.proj x, E.proj y⁆ := (t.map_lie _ _).symm
  have hle : (LieAlgebra.derivedSeries K E.L 1 : LieSubalgebra K E.L) ≤ t.range := by
    change (LieAlgebra.derivedSeries K E.L 1).toSubmodule ≤ t.range.toSubmodule
    rw [← LieIdeal.toLieSubalgebra_toSubmodule,
      LieAlgebra.coe_derivedSeries_one_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change ⁅x, y⁆ ∈ t.range
    rw [hbr]
    exact LieHom.mem_range_self t _
  have hge : t.range ≤ (LieAlgebra.derivedSeries K E.L 1 : LieSubalgebra K E.L) := by
    intro z hz
    obtain ⟨s, hs⟩ := hz
    rw [← hs]
    have hperfect : s ∈ LieAlgebra.derivedSeries K S 1 := by
      rw [killing_derivedSeries_one_eq_top]
      exact LieSubmodule.mem_top s
    have hmap : t s ∈ (LieAlgebra.derivedSeries K S 1).map t :=
      LieIdeal.mem_map hperfect
    exact LieIdeal.derivedSeries_map_le (f := t) 1 hmap
  have hrange : t.range = (LieAlgebra.derivedSeries K E.L 1 : LieSubalgebra K E.L) :=
    le_antisymm hge hle
  have hrange_set : (t.range : Set E.L) =
      (LieAlgebra.derivedSeries K E.L 1 : Set E.L) :=
    congrArg (fun P : LieSubalgebra K E.L => (P : Set E.L)) hrange
  exact (LieEquiv.ofInjective t (by
    intro x y h
    have hp := congrArg E.proj h
    simpa only [ht] using hp)).trans
      (LieEquiv.ofEq t.range (LieAlgebra.derivedSeries K E.L 1) hrange_set)

end ReductiveGroups
