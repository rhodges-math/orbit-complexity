import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientRootSpaces

/-!
# Center Quotient Subalgebra

Membership and root-space containment are faithfully detected in the
center quotient for subalgebras containing the original Cartan. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- The equivalence is

```lean
centerQuotientLieHom (K := K) x ∈ S.map (centerQuotientLieHom (K := K)) ↔
      x ∈ S
```
-/
theorem centerQuotient_mem_map_iff
    (S : LieSubalgebra K L) (hS : (LieAlgebra.center K L : LieSubalgebra K L) ≤ S)
    (x : L) :
    centerQuotientLieHom (K := K) x ∈ S.map (centerQuotientLieHom (K := K)) ↔
      x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (S.mem_map (centerQuotientLieHom (K := K)) _).mp hx
    have hc : x - y ∈ LieAlgebra.center K L := by
      rw [← centerQuotientLieHom_ker]
      change centerQuotientLieHom (K := K) (x - y) = 0
      rw [map_sub, hyx, sub_self]
    have hsum := S.add_mem (hS hc) hy
    simpa only [sub_add_cancel] using hsum
  · intro hx
    exact (S.mem_map (centerQuotientLieHom (K := K)) _).mpr ⟨x, hx, rfl⟩

/-- The equivalence is

```lean
(∀ z : L ⧸ LieAlgebra.center K L,
      z ∈ rootSpace (centerQuotientCartan H) χ →
      z ∈ S.map (centerQuotientLieHom (K := K))) ↔
    (∀ x : L, x ∈ rootSpace H (fun h => χ (centerQuotientCartanMap H h)) → x ∈ S)
```
-/
theorem centerQuotient_rootSpace_le_map_iff
    [IsAlgClosed K] [FiniteDimensional K L]
    (H S : LieSubalgebra K L) [H.IsCartanSubalgebra] (hHS : H ≤ S)
    (χ : centerQuotientCartan H → K) :
    (∀ z : L ⧸ LieAlgebra.center K L,
      z ∈ rootSpace (centerQuotientCartan H) χ →
      z ∈ S.map (centerQuotientLieHom (K := K))) ↔
    (∀ x : L, x ∈ rootSpace H (fun h => χ (centerQuotientCartanMap H h)) → x ∈ S) := by
  have hcenter : (LieAlgebra.center K L : LieSubalgebra K L) ≤ S :=
    (center_le_cartan H).trans hHS
  constructor
  · intro h x hx
    apply (centerQuotient_mem_map_iff S hcenter x).mp
    exact h _ (centerQuotientRootSpaceMap H χ ⟨x, hx⟩).property
  · intro h z hz
    obtain ⟨x, hx⟩ := centerQuotientRootSpaceMap_surjective H χ ⟨z, hz⟩
    have heq : centerQuotientLieHom (K := K) (x : L) = z :=
      congrArg Subtype.val hx
    rw [← heq]
    exact (centerQuotient_mem_map_iff S hcenter x).mpr (h x x.property)

end ReductiveGroups
