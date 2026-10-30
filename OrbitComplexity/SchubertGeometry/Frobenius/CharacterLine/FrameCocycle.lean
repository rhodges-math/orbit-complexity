import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.OverlapSquares

/-! # The inverse-character frame equation on the same union nodes -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter

private def singletonFrame {J : Type u} (j : J) : {s : Finset J // s.Nonempty} :=
  ⟨{j}, Finset.singleton_nonempty j⟩

private def frameRestriction {J : Type u} (u s : {s : Finset J // s.Nonempty})
    (k : J) (hk : k ∈ s.val) :
    unionIndex u (singletonFrame k) ⟶ unionIndex u s := by
  classical
  apply homOfLE
  change u.val ∪ {k} ⊆ u.val ∪ s.val
  exact Finset.union_subset Finset.subset_union_left
    (Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ hk))

private theorem inverse_unit_matching {A : Type u} [CommGroup A] (x y z : A)
    (h : z = y * x) (n : ℕ) : x⁻¹ ^ n = y ^ n * z⁻¹ ^ n := by
  have hy : y * (y * x)⁻¹ = x⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_comm y x⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  calc
    x⁻¹ ^ n = (y * (y * x)⁻¹) ^ n := congrArg (fun a ↦ a ^ n) hy.symm
    _ = y ^ n * z⁻¹ ^ n := by rw [← h, mul_pow]

/-- The candidate frame coefficients satisfy the line matching equation
on the specified union node. Every map is an original arrow of N; all powers
use the same retained units and coefficient ring. -/
theorem inverse_frame_overlap_cocycle {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (n : ℕ) (u s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val)
    (k : J) (hk : k ∈ s.val) (l : J) (hl : l ∈ s.val) :
    Units.map (N.map (frameRestriction u s k hk)).hom.toMonoidHom
        ((delta₀ (unionIndex u (singletonFrame k))
          j ((leOfHom (unionLeft u (singletonFrame k))) hj)
          k ((leOfHom (unionRight u (singletonFrame k))) (Finset.mem_singleton_self k)))⁻¹ ^ n) =
      Units.map (N.map (unionRight u s)).hom.toMonoidHom ((delta₀ s k hk l hl) ^ n) *
        Units.map (N.map (frameRestriction u s l hl)).hom.toMonoidHom
          ((delta₀ (unionIndex u (singletonFrame l))
            j ((leOfHom (unionLeft u (singletonFrame l))) hj)
            l ((leOfHom (unionRight u (singletonFrame l))) (Finset.mem_singleton_self l)))⁻¹ ^ n) :=
              by
  let w := unionIndex u s
  let hjw : j ∈ w.val := (leOfHom (unionLeft u s)) hj
  let hkw : k ∈ w.val := (leOfHom (unionRight u s)) hk
  let hlw : l ∈ w.val := (leOfHom (unionRight u s)) hl
  have hkmap : Units.map (N.map (frameRestriction u s k hk)).hom.toMonoidHom
      (delta₀ (unionIndex u (singletonFrame k))
        j ((leOfHom (unionLeft u (singletonFrame k))) hj)
        k ((leOfHom (unionRight u (singletonFrame k))) (Finset.mem_singleton_self k))) =
      delta₀ w j hjw k hkw :=
    hn _ _ (frameRestriction u s k hk) _ _ _ _
  have hlmap : Units.map (N.map (frameRestriction u s l hl)).hom.toMonoidHom
      (delta₀ (unionIndex u (singletonFrame l))
        j ((leOfHom (unionLeft u (singletonFrame l))) hj)
        l ((leOfHom (unionRight u (singletonFrame l))) (Finset.mem_singleton_self l))) =
      delta₀ w j hjw l hlw :=
    hn _ _ (frameRestriction u s l hl) _ _ _ _
  have hklmap : Units.map (N.map (unionRight u s)).hom.toMonoidHom
      (delta₀ s k hk l hl) = delta₀ w k hkw l hlw :=
    hn _ _ (unionRight u s) _ _ _ _
  simp only [map_pow, map_inv, hkmap, hlmap, hklmap]
  exact inverse_unit_matching _ _ _ (hco w j hjw k hkw l hlw) n

end SchubertGeometry.RetainedCharacter
