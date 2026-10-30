import OrbitComplexity.SchubertGeometry.FlagVariety.Points

/-! # Subgroup charts on rational flags

A subgroup meeting the Borel only at the identity maps injectively to the flag space.
The image of a subset under the flag projection has the expected right Borel saturation.

## Main results

* `SchubertGeometry.flagProjection_injective`: injectivity for a subgroup disjoint from the Borel.
* `SchubertGeometry.flagProjection_preimage`: the preimage of a projected set is its saturation.
-/

open scoped Pointwise

namespace SchubertGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- A subgroup disjoint from the Borel has distinct flag cosets for distinct points. -/
theorem flagProjection_injective (U : Subgroup G.points) (hU : U ⊓ G.borelPoints = ⊥) :
    Function.Injective (fun u : U => flagProjection G u) := by
  intro u v huv
  apply Subtype.ext
  have hB := (flagProjection_eq_iff G u v).mp huv
  have hmem : (u : G.points)⁻¹ * v ∈ U ⊓ G.borelPoints :=
    ⟨U.mul_mem (U.inv_mem u.property) v.property, hB⟩
  rw [hU] at hmem
  have hone : (u : G.points)⁻¹ * v = 1 := hmem
  exact inv_mul_eq_one.mp hone

/-- The full inverse image of projected points is their right Borel saturation. -/
theorem flagProjection_preimage (s : Set G.points) :
    flagProjection G ⁻¹' (flagProjection G '' s) = s * (G.borelPoints : Set G.points) :=
  QuotientGroup.preimage_image_mk_eq_mul G.borelPoints s

/-- Left translation by a group point is a homeomorphism of rational flags. -/
def flagTranslation (g : G.points) : flagPoints G ≃ₜ flagPoints G := Homeomorph.smul g

/-- Translation on rational flags agrees with the standard left group action. -/
theorem flagTranslation_apply (g : G.points) (x : flagPoints G) :
    flagTranslation G g x = g • x := rfl

end

end SchubertGeometry
