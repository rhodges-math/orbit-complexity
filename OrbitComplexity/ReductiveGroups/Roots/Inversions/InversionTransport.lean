import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionCone
import OrbitComplexity.ReductiveGroups.RootClosure.Equivariance

/-!
# Weyl transport of inversion cones

The image `a • IL(d)` under Mathlib's Weyl action inherits
integral-cone closure and independence. Applying the inverse action reduces
the cone assertion to the prescribed-partial-sum proof in `InversionCone`.

Positivity of the transported image under length additivity is
`Roots/InversionProduct.lean`; the comparison with the root characters of a
reductive group is `Groups/BorelRootSystemBridge.lean`.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The Weyl action expressed as its existing weight-space linear equivalence. -/
def weylRootLinearEquiv (a : P.weylGroup) : M ≃ₗ[R] M :=
  RootPairing.Equiv.weightHom P a.val

/-- The equality is

```lean
weylRootLinearEquiv a β = a • β
```
-/
@[simp]
theorem weylRootLinearEquiv_apply (a : P.weylGroup) (β : M) :
    weylRootLinearEquiv a β = a • β := rfl

/-- Membership in the Weyl image is tested by the inverse action. -/
theorem mem_weyl_image_iff_inv_smul_mem (a : P.weylGroup) (S : Set M) (β : M) :
    β ∈ (fun γ : M => a • γ) '' S ↔ a⁻¹ • β ∈ S := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    simpa only [inv_smul_smul] using hγ
  · intro hβ
    exact ⟨a⁻¹ • β, hβ, smul_inv_smul a β⟩

/-- Applying the inverse Weyl action to a finite natural sum preserves its coefficients. -/
theorem weyl_inv_smul_nat_sum {κ : Type*} (a : P.weylGroup) (t : Finset κ)
    (n : κ → ℕ) (β : κ → M) :
    a⁻¹ • (∑ k ∈ t, n k • β k) = ∑ k ∈ t, n k • (a⁻¹ • β k) := by
  change weylRootLinearEquiv a⁻¹ (∑ k ∈ t, n k • β k) = _
  simp only [map_sum, map_nsmul, weylRootLinearEquiv_apply]

/-- The nonnegative integral span commutes with the Weyl action. -/
theorem weyl_image_addSubmonoidClosure (a : P.weylGroup) (S : Set M) :
    (fun γ : M => a • γ) '' (AddSubmonoid.closure S : Set M) =
      (AddSubmonoid.closure ((fun γ : M => a • γ) '' S) : Set M) := by
  change (weylRootLinearEquiv a).toAddEquiv '' (AddSubmonoid.closure S : Set M) =
    (AddSubmonoid.closure ((weylRootLinearEquiv a).toAddEquiv '' S) : Set M)
  simpa only [AddSubmonoid.coe_map, AddEquiv.coe_toAddMonoidHom] using
    congrArg (fun T : AddSubmonoid M => (T : Set M))
      (AddMonoidHom.map_mclosure (weylRootLinearEquiv a).toAddEquiv.toAddMonoidHom S)

/-- The equivalence is

```lean
β ∈ AddSubmonoid.closure ((fun γ : M => a • γ) '' S) ↔
      a⁻¹ • β ∈ AddSubmonoid.closure S
```
-/
theorem mem_weyl_imageClosure_iff_inv_smul_mem (a : P.weylGroup) (S : Set M) (β : M) :
    β ∈ AddSubmonoid.closure ((fun γ : M => a • γ) '' S) ↔
      a⁻¹ • β ∈ AddSubmonoid.closure S := by
  change β ∈ (AddSubmonoid.closure ((fun γ : M => a • γ) '' S) : Set M) ↔ _
  rw [← weyl_image_addSubmonoidClosure]
  exact mem_weyl_image_iff_inv_smul_mem a _ β

/-- An injective Weyl action preserves independence of a set of vectors. -/
theorem weyl_image_linearIndepOn (a : P.weylGroup) {S : Set M}
    (hS : LinearIndepOn R id S) : LinearIndepOn R id ((fun β : M => a • β) '' S) := by
  exact hS.id_imageₛ (f := (weylRootLinearEquiv a).toLinearMap)
    (weylRootLinearEquiv a).injective.injOn

variable [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic]

/-- A root in the integral cone on the transported inversions is one of those
transported inversions. The inverse root is tested in the original inversion cone. -/
theorem root_mem_weyl_image_inversionClosure_iff (b : P.Base)
    (a d : P.weylGroup) (i : ι) :
    P.root i ∈ AddSubmonoid.closure ((fun β : M => a • β) '' leftRootInversions b d) ↔
      P.root i ∈ (fun β : M => a • β) '' leftRootInversions b d := by
  rw [mem_weyl_imageClosure_iff_inv_smul_mem, mem_weyl_image_iff_inv_smul_mem,
    P.weylGroup_apply_root, root_mem_inversionClosure_iff]

/-- In the inverse-action step, the resulting root is positive.
This follows from membership in the original left inversion set. -/
theorem InversionTransport.isPos_of_mem_weyl_image_inversionClosure (b : P.Base)
    (a d : P.weylGroup) (i : ι)
    (hi : P.root i ∈
      AddSubmonoid.closure ((fun β : M => a • β) '' leftRootInversions b d)) :
    b.IsPos (P.weylGroupToPerm a⁻¹ i) := by
  have hmem := (root_mem_weyl_image_inversionClosure_iff b a d i).mp hi
  rw [mem_weyl_image_iff_inv_smul_mem, P.weylGroup_apply_root,
    root_mem_leftRootInversions] at hmem
  exact hmem.1

/-- The transported cone assertion with finite natural coefficients spelled out. -/
theorem InversionTransport.mem_weyl_image_inversions_iff_finite_sum (b : P.Base)
    (a d : P.weylGroup) (i : ι) :
    P.root i ∈ (fun β : M => a • β) '' leftRootInversions b d ↔
      ∃ (t : Finset M) (n : M → ℕ),
        (↑t : Set M) ⊆ (fun β : M => a • β) '' leftRootInversions b d ∧
          ∑ β ∈ t, n β • β = P.root i := by
  rw [← root_mem_weyl_image_inversionClosure_iff b a d i,
    mem_addSubmonoidClosure_iff_finite_sum]

variable [P.IsRootSystem] [P.IsReduced]

/-- The Weyl image of inversions of a distinct-simple word is independent. -/
theorem InversionTransport.inversions_simpleWeylWord_linearIndepOn (b : P.Base)
    (a : P.weylGroup) (l : List b.support) (hl : l.Nodup) :
    LinearIndepOn R id
      ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)) :=
  weyl_image_linearIndepOn a (LeftRootInversions.simpleWeylWord_linearIndepOn b l hl)

/-- A natural expression for a root using transported inversions has total
multiplicity one. The indexing subtype is the image set. -/
theorem InversionTransport.image_inversion_natCoefficientSum_eq_one (b : P.Base)
    (a : P.weylGroup) (l : List b.support) (hl : l.Nodup)
    (t : Finset ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)))
    (n : ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)) → ℕ)
    (i : ι) (hsum : ∑ δ ∈ t, n δ • (δ : M) = P.root i) :
    ∑ δ ∈ t, n δ = 1 := by
  have hi : P.root i ∈
      (fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l) := by
    apply (root_mem_weyl_image_inversionClosure_iff b a (simpleWeylWord b l) i).mp
    rw [← hsum]
    exact AddSubmonoid.sum_mem _ (fun δ _ =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure δ.property) _)
  exact NatCoefficientSum.eq_one_of_linearIndepOn
    (InversionTransport.inversions_simpleWeylWord_linearIndepOn b a l hl) t n hi hsum

/-- No natural sum of at least two transported inversions is any root.
Repeated copies count toward this total multiplicity. -/
theorem weyl_image_inversion_natSum_not_root (b : P.Base)
    (a : P.weylGroup) (l : List b.support) (hl : l.Nodup)
    (t : Finset ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)))
    (n : ((fun β : M => a • β) '' leftRootInversions b (simpleWeylWord b l)) → ℕ)
    (hn : 2 ≤ ∑ δ ∈ t, n δ) : (∑ δ ∈ t, n δ • (δ : M)) ∉ Set.range P.root := by
  rintro ⟨i, hi⟩
  have he := InversionTransport.image_inversion_natCoefficientSum_eq_one b a l hl t n i hi.symm
  omega

end ReductiveGroups
