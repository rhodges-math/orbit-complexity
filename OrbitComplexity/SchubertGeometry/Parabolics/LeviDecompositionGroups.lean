import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionPoints
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SemidirectProduct

/-! # Internal semidirect products of parabolic point groups

Unique Levi factors and normality identify the parabolic point group with its internal
semidirect product and give the group projection onto the Levi.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem levi_le (I : Set G.rootBase.support) :
    G.leviPoints I ≤ standardParabolicPoints G I := by
  rw [parabolic_eq_levi_sup_unipotent]
  exact le_sup_left

/-- The Levi subgroup inside the standard parabolic point group. -/
abbrev leviInParabolic (I : Set G.rootBase.support) : Subgroup (standardParabolicPoints G I) :=
  (G.leviPoints I).subgroupOf (standardParabolicPoints G I)

/-- The outside-subsystem root group inside the standard parabolic point group. -/
abbrev unipotentInParabolic (I : Set G.rootBase.support) :
    Subgroup (standardParabolicPoints G I) :=
  (parabolicUnipotentPoints G I).subgroupOf (standardParabolicPoints G I)

/-- The two factors are complementary subgroups of the parabolic point group. -/
theorem parabolicComplement (I : Set G.rootBase.support) :
    (leviInParabolic G I).IsComplement' (unipotentInParabolic G I) := by
  apply Subgroup.isComplement_iff_existsUnique.mpr
  intro g
  obtain ⟨p, ⟨hl, hu, he⟩, huniq⟩ := parabolic_existsUnique_levi_mul G I g.val g.property
  have huP : p.2 ∈ standardParabolicPoints G I := by
    rw [parabolic_eq_levi_sup_unipotent]
    exact (show parabolicUnipotentPoints G I ≤ _ from le_sup_right) hu
  let l : leviInParabolic G I := ⟨⟨p.1, levi_le G I hl⟩, hl⟩
  let u : unipotentInParabolic G I := ⟨⟨p.2, huP⟩, hu⟩
  refine ⟨(l, u), Subtype.ext he, ?_⟩
  rintro ⟨l', u'⟩ hmul
  have hraw : l'.val.val * u'.val.val = g.val := congrArg Subtype.val hmul
  have hp := huniq (l'.val.val, u'.val.val) ⟨l'.property, u'.property, hraw⟩
  exact Prod.ext (Subtype.ext (Subtype.ext (congrArg Prod.fst hp)))
    (Subtype.ext (Subtype.ext (congrArg Prod.snd hp)))

/-- The parabolic point group projects homomorphically onto its Levi factor. -/
def parabolicPointProjection (I : Set G.rootBase.support) :
    standardParabolicPoints G I →* G.leviPoints I :=
  ((Subgroup.subgroupOfEquivOfLe (levi_le G I)).toMonoidHom).comp
    (((parabolicComplement G I).QuotientMulEquiv).toMonoidHom.comp
      (QuotientGroup.mk' (unipotentInParabolic G I)))

/-- The point projection restricts to the identity on the included Levi. -/
theorem parabolicPointProjection_levi (I : Set G.rootBase.support) (l : G.leviPoints I) :
    parabolicPointProjection G I (Subgroup.inclusion (levi_le G I) l) = l := by
  let e := (parabolicComplement G I).QuotientMulEquiv
  let x : leviInParabolic G I := ⟨Subgroup.inclusion (levi_le G I) l, l.property⟩
  have he : e ((QuotientGroup.mk' (unipotentInParabolic G I)) x.val) = x := by
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  exact congrArg (Subgroup.subgroupOfEquivOfLe (levi_le G I)) he

/-- The kernel of the Levi point projection is the outside-subsystem root subgroup. -/
theorem parabolicPointProjection_ker (I : Set G.rootBase.support) :
    (parabolicPointProjection G I).ker = unipotentInParabolic G I := by
  let e := (parabolicComplement G I).QuotientMulEquiv.trans
    (Subgroup.subgroupOfEquivOfLe (levi_le G I))
  ext g
  change e ((QuotientGroup.mk' (unipotentInParabolic G I)) g) = 1 ↔ g ∈ _
  constructor
  · intro hg
    have hq : (QuotientGroup.mk' (unipotentInParabolic G I)) g = 1 :=
      e.injective (hg.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff g).mp hq
  · intro hg
    have hq : (QuotientGroup.mk' (unipotentInParabolic G I)) g = 1 :=
      (QuotientGroup.eq_one_iff g).mpr hg
    rw [hq, map_one]

/-- The Levi projection extracts the first factor of a parabolic factorization. -/
theorem parabolicPointProjection_factors (I : Set G.rootBase.support)
    (p : standardParabolicPoints G I) (l : G.leviPoints I)
    (u : parabolicUnipotentPoints G I) (he : (l : G.points) * u = p) :
    parabolicPointProjection G I p = l := by
  have hUP : parabolicUnipotentPoints G I ≤ standardParabolicPoints G I := by
    rw [parabolic_eq_levi_sup_unipotent]
    exact le_sup_right
  let lp := Subgroup.inclusion (levi_le G I) l
  let up := Subgroup.inclusion hUP u
  have heP : lp * up = p := Subtype.ext he
  have hu : parabolicPointProjection G I up = 1 := by
    change up ∈ (parabolicPointProjection G I).ker
    rw [parabolicPointProjection_ker]
    exact u.property
  calc
    _ = parabolicPointProjection G I (lp * up) :=
      congrArg (parabolicPointProjection G I) heP.symm
    _ = parabolicPointProjection G I lp * parabolicPointProjection G I up := map_mul _ _ _
    _ = l * 1 := congrArg₂ (· * ·) (parabolicPointProjection_levi G I l) hu
    _ = l := mul_one l

/-- The parabolic group is the internal semidirect product of its normal root group and Levi. -/
def parabolicSemidirectIso (I : Set G.rootBase.support) :
    (unipotentInParabolic G I) ⋊[
      ((unipotentInParabolic G I).normalizerMonoidHom).comp (Subgroup.inclusion
        ((unipotentInParabolic G I).normalizer_eq_top ▸ le_top))]
      (leviInParabolic G I) ≃* standardParabolicPoints G I :=
  SemidirectProduct.mulEquivSubgroup (parabolicComplement G I).symm

end SchubertGeometry
