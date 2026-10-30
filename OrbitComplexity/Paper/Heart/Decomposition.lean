import OrbitComplexity.Paper.Heart.VdPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootIdealTransport
import OrbitComplexity.GroupActions.Varieties.RootProductPoints
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# Closed subgroups in the heart decomposition

The conjugate minimal-factor subgroup has the heart root support. It is a closed
subgroup of the inversion-root group, normalized by the torus. Multiplication with
the parabolic inversion-root group in either order is an isomorphism of varieties.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits.Vd
open ReductiveGroups TauCeti CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The defining Hopf ideal of the conjugate subgroup V_d=aU_da⁻¹. -/
def ideal (I : Set G.rootBase.support) (w : G.weylGroup) : HopfIdeal K G.coordinateAlgebra :=
  (G.rootSubsetIdeal
    (leftRootInversionIndices G.rootBase (leftParabolicRepresentative G.rootBase I w))
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).conjugate
      (G.weylPoint (leftParabolicFactor G.rootBase I w))

/-- The conjugate defining ideal equals the defining ideal of the heart root support. -/
theorem ideal_eq_rootSubset (I : Set G.rootBase.support) (w : G.weylGroup) :
    ideal G I w = G.rootSubsetIdeal (heartRootIndices G I w) (heartRootIndices_closed G I w) := by
  apply G.rootSubsetIdeal_weyl_conj
  · intro r hr
    exact (mem_leftRootInversionIndices G.rootBase _ r).mp hr |>.1
  · intro r hr
    exact hr.1
  · exact heartRootIndices_eq_image G I w

private def conjugateEquivOfEq (A J : HopfIdeal K G.coordinateAlgebra)
    (g : G.points) (h : A.conjugate g = J) :
    (G.coordinateAlgebra ⧸ J.toIdeal) ≃ₐc[K] (G.coordinateAlgebra ⧸ A.toIdeal) := by
  rw [← h]
  exact conjugateQuotientEquiv A g

omit [IsAlgClosed K] [CharZero K] in
private theorem conjugateEquivOfEq_mk (A J : HopfIdeal K G.coordinateAlgebra)
    (g : G.points) (h : A.conjugate g = J) (b : G.coordinateAlgebra) :
    conjugateEquivOfEq G A J g h (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk A.toIdeal (HopfAlgebra.pointConjugationAlgHom g b) := by
  subst J
  exact conjugateQuotientEquiv_mk A g b

/-- Coordinate conjugation identifies the heart subgroup with its minimal-factor subgroup. -/
def coordinateConjugation (I : Set G.rootBase.support) (w : G.weylGroup) :
    G.rootSubsetAlgebra (heartRootIndices G I w) (heartRootIndices_closed G I w) ≃ₐc[K]
      G.rootSubsetAlgebra
        (leftRootInversionIndices G.rootBase (leftParabolicRepresentative G.rootBase I w))
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) :=
  conjugateEquivOfEq G _ _ (G.weylPoint (leftParabolicFactor G.rootBase I w))
    (ideal_eq_rootSubset G I w)

/-- The heart-to-minimal-factor coordinate map is Weyl-point conjugation. -/
theorem coordinateConjugation_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (b : G.coordinateAlgebra) :
    coordinateConjugation G I w (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (HopfAlgebra.pointConjugationAlgHom
        (G.weylPoint (leftParabolicFactor G.rootBase I w)) b) :=
  conjugateEquivOfEq_mk G _ _ _ _ b

/-- The conjugate subgroup V_d with its closed affine variety structure. -/
abbrev variety (I : Set G.rootBase.support) (w : G.weylGroup) : GroupActions.Variety K :=
  GroupActions.rootSubsetVariety G (heartRootIndices G I w) (heartRootIndices_closed G I w)

private theorem heart_le_inversions (I : Set G.rootBase.support) (w : G.weylGroup) :
    heartRootIndices G I w ⊆ leftRootInversionIndices G.rootBase w := by
  intro r hr
  rw [inversionRoots_eq_union_heart G I w]
  exact Or.inr hr

/-- The heart subgroup is a closed subgroup of the inversion-root group U_w. -/
def inclusion (I : Set G.rootBase.support) (w : G.weylGroup) :
    (variety G I w).toOver ⟶
      (GroupActions.rootSubsetVariety G (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).toOver :=
  (CommHopfAlgCat.quotientSpecMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra)
    (G.rootSubsetIdeal_anti _ _ (heartRootIndices_closed G I w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
      (heart_le_inversions G I w))).hom.hom

/-- The inclusion of V_d into U_w is a closed immersion. -/
instance inclusion_isClosed (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsClosedImmersion (inclusion G I w).left := by
  change IsClosedImmersion (CommHopfAlgCat.quotientSpecMapOfLe
    (CommHopfAlgCat.of K G.coordinateAlgebra) _).hom.hom.left
  infer_instance

/-- The inclusion of V_d into U_w is a homomorphism of group objects. -/
instance inclusion_isMonHom (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsMonHom (inclusion G I w) := by
  change IsMonHom (CommHopfAlgCat.quotientSpecMapOfLe
    (CommHopfAlgCat.of K G.coordinateAlgebra) _).hom.hom
  infer_instance

/-- Inclusion of Vd in Uw followed by the ambient inclusion is its closed subgroup inclusion. -/
theorem inclusion_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    inclusion G I w ≫ GroupActions.rootSubsetInclusion G
        (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) =
      GroupActions.rootSubsetInclusion G (heartRootIndices G I w)
        (heartRootIndices_closed G I w) := by
  have h := CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι
    (CommHopfAlgCat.of K G.coordinateAlgebra)
    (G.rootSubsetIdeal_anti _ _ (heartRootIndices_closed G I w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
      (heart_le_inversions G I w))
  exact congrArg (fun f => f.hom.hom) h

/-- Multiplication Ua × Vd → Uw is an isomorphism of affine varieties. -/
def multiplicationIso (I : Set G.rootBase.support) (w : G.weylGroup) :
    (GroupActions.rootProductVariety G
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (heartRootIndices G I w) (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
      (heartRootIndices_closed G I w)).toOver ≅
        (GroupActions.rootSubsetVariety G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).toOver :=
  GroupActions.rootProductIso G _ _ _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
    (heartRootIndices_closed G I w) (inversionRoots_eq_union_heart G I w)
    (inversionRoots_disjoint_heart G I w)

/-- Multiplication Vd × Ua → Uw is an isomorphism of affine varieties. -/
def reverseMultiplicationIso (I : Set G.rootBase.support) (w : G.weylGroup) :
    (GroupActions.rootProductVariety G (heartRootIndices G I w)
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (heartRootIndices_closed G I w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toOver ≅
        (GroupActions.rootSubsetVariety G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).toOver :=
  GroupActions.rootProductIso G _ _ _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (heartRootIndices_closed G I w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
    ((inversionRoots_eq_union_heart G I w).trans (Set.union_comm _ _))
    (inversionRoots_disjoint_heart G I w).symm

/-- The first product isomorphism is the restriction of ambient multiplication. -/
theorem multiplicationIso_hom_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    (multiplicationIso G I w).hom ≫
        GroupActions.rootSubsetInclusion G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) =
      (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (GroupActions.affineMulMap
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal)
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal (heartRootIndices G I w)
          (heartRootIndices_closed G I w)).toIdeal))).op :=
  GroupActions.rootProductIso_hom_comp G _ _ _ _ _ _ _ _

/-- The reversed product isomorphism is the restriction of ambient multiplication. -/
theorem reverseMultiplicationIso_hom_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    (reverseMultiplicationIso G I w).hom ≫
        GroupActions.rootSubsetInclusion G (leftRootInversionIndices G.rootBase w)
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) =
      (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (GroupActions.affineMulMap
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal (heartRootIndices G I w)
          (heartRootIndices_closed G I w)).toIdeal)
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)).toIdeal))).op :=
  GroupActions.rootProductIso_hom_comp G _ _ _ _ _ _ _ _

end SchubertOrbits.Vd

namespace SchubertOrbits
open ReductiveGroups TauCeti CategoryTheory AlgebraicGeometry
universe v
variable {K : Type v} [Field K] [IsAlgClosed K] [CharZero K]

/-- The conjugate minimal-factor subgroup is closed, torus-normalized, lies in `U_w` and
directly spans `U_w`. -/
theorem directlySpannedUw (G : ReductiveGroupData K)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    Vd.ideal G I w =
        G.rootSubsetIdeal (heartRootIndices G I w) (heartRootIndices_closed G I w) ∧
    IsClosedImmersion (Vd.inclusion G I w).left ∧
    IsMonHom (Vd.inclusion G I w) ∧
    G.torusPoints ≤ Subgroup.normalizer (Vd.points G I w : Set G.points) ∧
    Vd.points G I w ≤ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) ∧
    (∀ (g : G.points),
      g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →
      ∃! p : G.points × G.points,
        p.1 ∈ G.rootSubsetPoints
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
        p.2 ∈ Vd.points G I w ∧ p.1 * p.2 = g) ∧
    (∀ (g : G.points),
      g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →
      ∃! p : G.points × G.points,
        p.1 ∈ Vd.points G I w ∧
        p.2 ∈ G.rootSubsetPoints
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
        p.1 * p.2 = g) :=
  ⟨Vd.ideal_eq_rootSubset G I w, inferInstance, inferInstance,
    Vd.torus_le_normalizer G I w, Vd.points_le_inversions G I w, Vd.existsUnique_mul G I w,
    Vd.existsUnique_mul_rev G I w⟩

/-- Closedness, torus normalization and both direct spanning statements over the complex numbers. -/
theorem directlySpannedUw_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    Vd.ideal G I w =
        G.rootSubsetIdeal (heartRootIndices G I w) (heartRootIndices_closed G I w) ∧
    IsClosedImmersion (Vd.inclusion G I w).left ∧
    IsMonHom (Vd.inclusion G I w) ∧
    G.torusPoints ≤ Subgroup.normalizer (Vd.points G I w : Set G.points) ∧
    Vd.points G I w ≤ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) ∧
    (∀ (g : G.points),
      g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →
      ∃! p : G.points × G.points,
        p.1 ∈ G.rootSubsetPoints
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
        p.2 ∈ Vd.points G I w ∧ p.1 * p.2 = g) ∧
    (∀ (g : G.points),
      g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →
      ∃! p : G.points × G.points,
        p.1 ∈ Vd.points G I w ∧
        p.2 ∈ G.rootSubsetPoints
          (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
          (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ∧
        p.1 * p.2 = g) :=
  directlySpannedUw G I w

end SchubertOrbits
