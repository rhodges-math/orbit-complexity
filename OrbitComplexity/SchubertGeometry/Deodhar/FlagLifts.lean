import OrbitComplexity.SchubertGeometry.FlagVariety.BorelStabilizer
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Regular differences of flag lifts

Two group-valued morphisms representing the same flag differ by a regular Borel-valued
morphism. Reduced-source factorization upgrades pointwise Borel membership to a morphism.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapDifference {X H : GroupActions.Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (p : X.points) :
    GroupActions.Variety.mapPoints (f⁻¹ * g) p =
      (GroupActions.Variety.mapPoints f p)⁻¹ * GroupActions.Variety.mapPoints g p := by
  apply H.pointsEquivOverHom.injective
  rw [GroupActions.Variety.pointsEquivOverHom_mul,
    GroupActions.Variety.pointsEquivOverHom_inv]
  change X.pointsEquivOverHom p ≫ (f⁻¹ * g) =
    (X.pointsEquivOverHom p ≫ f)⁻¹ * (X.pointsEquivOverHom p ≫ g)
  rw [MonObj.comp_mul, GrpObj.comp_inv]

variable (X : GroupActions.Variety K)
  (f g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
  (hf : f ≫ flagQuotientMorphism G = g ≫ flagQuotientMorphism G)
include hf

private theorem difference_mem (p : X.points) :
    Set.range (GroupActions.Variety.mapPoints (GroupActions.borelInclusion G))
      (GroupActions.Variety.mapPoints (f⁻¹ * g) p) := by
  let a := (GroupActions.reductivePointsMulEquiv G).symm
    (GroupActions.Variety.mapPoints f p)
  let b := (GroupActions.reductivePointsMulEquiv G).symm
    (GroupActions.Variety.mapPoints g p)
  have ha : GroupActions.reductivePointsEquiv G a =
      GroupActions.Variety.mapPoints f p :=
    (GroupActions.reductivePointsMulEquiv G).apply_symm_apply _
  have hb : GroupActions.reductivePointsEquiv G b =
      GroupActions.Variety.mapPoints g p :=
    (GroupActions.reductivePointsMulEquiv G).apply_symm_apply _
  have hq := congrArg (fun j => GroupActions.Variety.mapPoints j p) hf
  rw [GroupActions.Variety.mapPoints_comp, GroupActions.Variety.mapPoints_comp,
    ← ha, ← hb, flagQuotientMorphism_points, flagQuotientMorphism_points] at hq
  have hm := (flagProjection_eq_iff G a b).mp ((flagVarietyPointsEquiv G).injective hq)
  let c := (GroupActions.borelPointsMulEquiv G).symm ⟨a⁻¹ * b, hm⟩
  refine ⟨c, ?_⟩
  have hc : (GroupActions.borelPointsMulEquiv G c : G.points) = a⁻¹ * b :=
    congrArg Subtype.val ((GroupActions.borelPointsMulEquiv G).apply_symm_apply _)
  rw [GroupActions.borelInclusion_points, hc, mapDifference, ← ha, ← hb]
  exact (map_mul (GroupActions.reductivePointsMulEquiv G) a⁻¹ b).trans
    (congrArg₂ (fun x y => x * y)
      (map_inv (GroupActions.reductivePointsMulEquiv G) a) rfl)

private theorem difference_range : Set.range (f⁻¹ * g).left ⊆
    Set.range (GroupActions.borelInclusion G).left :=
  GroupActions.Variety.range_subset_of_mapPoints (f⁻¹ * g)
    (GroupActions.borelInclusion G) (by rintro _ ⟨p, rfl⟩; exact difference_mem G X f g hf p)

/-- The regular Borel-valued difference of two group-valued lifts of one flag morphism. -/
def borelDifference : X.toOver ⟶ (GroupActions.borelVariety G).toOver := by
  let d : X.scheme ⟶ (GroupActions.reductiveVariety G).scheme := (f⁻¹ * g).left
  let i : (GroupActions.borelVariety G).scheme ⟶
      (GroupActions.reductiveVariety G).scheme := (GroupActions.borelInclusion G).left
  have hr : Set.range d ⊆ Set.range i := difference_range G X f g hf
  let b := GroupActions.liftPreimmersion i d hr
  have hb : b ≫ i = d := GroupActions.liftPreimmersion_fac i d hr
  exact Over.homMk b (by
    change b ≫ (GroupActions.borelVariety G).toSpec = X.toSpec
    rw [← (show i ≫ (GroupActions.reductiveVariety G).toSpec =
      (GroupActions.borelVariety G).toSpec from (GroupActions.borelInclusion G).w),
      ← Category.assoc, hb]
    exact (f⁻¹ * g).w)

/-- The Borel difference includes into the group as the quotient of its two lifts. -/
theorem borelDifference_inclusion :
    borelDifference G X f g hf ≫ GroupActions.borelInclusion G = f⁻¹ * g := by
  apply Over.OverMorphism.ext
  let d : X.scheme ⟶ (GroupActions.reductiveVariety G).scheme := (f⁻¹ * g).left
  let i : (GroupActions.borelVariety G).scheme ⟶
      (GroupActions.reductiveVariety G).scheme := (GroupActions.borelInclusion G).left
  change GroupActions.liftPreimmersion i d (difference_range G X f g hf) ≫ i = d
  exact GroupActions.liftPreimmersion_fac i d _

/-- Multiplication by the Borel difference changes the first flag lift to the second. -/
theorem borelDifference_mul :
    f * (borelDifference G X f g hf ≫ GroupActions.borelInclusion G) = g := by
  rw [borelDifference_inclusion, mul_inv_cancel_left]

end
end SchubertGeometry
