import OrbitComplexity.Paper.Heart.Conjugation
import OrbitComplexity.Paper.Heart.Embedding

/-!
# Translation between the heart and the minimal Schubert cell

The left parabolic factor translates the minimal Schubert cell onto the heart.
The inverse isomorphism restricts inverse left translation on the flag variety.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits
open ReductiveGroups TauCeti GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem weylFlag_mul (a b : G.weylGroup) :
    flagProjection G (G.weylPoint a * G.weylPoint b) =
      flagProjection G (G.weylPoint (a * b)) := by
  obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.weylElementPoint_mul G.rootBase a b
  have he' : G.weylPoint a * G.weylPoint b = t * G.weylPoint (a * b) := by
    simpa only [G.weylPoint_eq] using he
  apply (flagProjection_eq_iff G _ _).mpr
  rw [he', mul_inv_rev]
  exact G.torus_le_borel ((Subgroup.mem_normalizer_iff''.mp
    (G.weylPoint_mem_normalizer (a * b)) t⁻¹).mp (G.torusPoints.inv_mem ht))

private theorem weylFlag_conjugate (a b : G.weylGroup) (u : G.points) :
    flagProjection G ((G.weylPoint a * u * (G.weylPoint a)⁻¹) * G.weylPoint (a * b)) =
      G.weylPoint a • flagProjection G (u * G.weylPoint b) := by
  let v := G.weylPoint a * u * (G.weylPoint a)⁻¹
  have h := congrArg (fun q : flagPoints G => v • q) (weylFlag_mul G a b)
  change flagProjection G (v * (G.weylPoint a * G.weylPoint b)) =
    flagProjection G (v * G.weylPoint (a * b)) at h
  calc
    _ = flagProjection G (v * (G.weylPoint a * G.weylPoint b)) := h.symm
    _ = _ := by
      change flagProjection G (v * (G.weylPoint a * G.weylPoint b)) =
        flagProjection G (G.weylPoint a * (u * G.weylPoint b))
      congr 1
      dsimp only [v]
      group

/-- Weyl conjugation of a minimal-factor root point gives its translated heart flag. -/
theorem heartFlag_translate (I : Set G.rootBase.support) (w : G.weylGroup) (u : G.points) :
    flagProjection G
      ((G.weylPoint (leftParabolicFactor G.rootBase I w) * u *
        (G.weylPoint (leftParabolicFactor G.rootBase I w))⁻¹) * G.weylPoint w) =
      G.weylPoint (leftParabolicFactor G.rootBase I w) •
        flagProjection G (u * G.weylPoint (leftParabolicRepresentative G.rootBase I w)) := by
  have h := weylFlag_conjugate G (leftParabolicFactor G.rootBase I w)
    (leftParabolicRepresentative G.rootBase I w) u
  simpa only [← leftParabolic_factorization G.rootBase I w] using h

/-- The root conjugation map followed by the heart chart is ambient translation. -/
theorem heartRoot_translate (I : Set G.rootBase.support) (w : G.weylGroup) :
    (minimalToVdIso G I w).hom ≫ heartRootMorphism G I w =
      schubertRootMorphism G (leftParabolicRepresentative G.rootBase I w) ≫
        Variety.translateMorphism (reductiveVariety G) (flagVariety G)
          (reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w))) := by
  apply Variety.mapPoints_injective
  funext x
  rw [Variety.mapPoints_comp, Variety.mapPoints_comp,
    heartRootMorphism_points, minimalToVdIso_points,
    Variety.mapPoints_translateMorphism, schubertRootMorphism_points]
  exact (congrArg (flagVarietyPointsEquiv G) (heartFlag_translate G I w _)).trans
    (flagVarietyAction_points G _ _).symm

/-- Translation identifies the minimal-factor Schubert cell with the I-heart. -/
def heartTranslationIso (I : Set G.rootBase.support) (w : G.weylGroup) :
    (schubertCell G (leftParabolicRepresentative G.rootBase I w)).toOver ≅
      (heart G I w).toOver :=
  (schubertCellIso G (leftParabolicRepresentative G.rootBase I w)).symm ≪≫
    minimalToVdIso G I w ≪≫ heartIso G I w

/-- The heart isomorphism into the flag variety is translation by the parabolic factor. -/
theorem heartTranslationIso_hom_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    (heartTranslationIso G I w).hom ≫ heartInclusion G I w =
      schubertCellInclusion G (leftParabolicRepresentative G.rootBase I w) ≫
        (Variety.translationIso (reductiveVariety G) (flagVariety G)
          (reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)))).hom := by
  apply (cancel_epi (schubertCellIso G (leftParabolicRepresentative G.rootBase I w)).hom).mp
  simp only [heartTranslationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, heartIso_hom_comp]
  rw [← Category.assoc, schubertCellIso_hom_comp]
  exact heartRoot_translate G I w

/-- The heart-to-minimal-cell isomorphism is the inverse translation. -/
def heartMinimalIso (I : Set G.rootBase.support) (w : G.weylGroup) :
    (heart G I w).toOver ≅
      (schubertCell G (leftParabolicRepresentative G.rootBase I w)).toOver :=
  (heartTranslationIso G I w).symm

/-- The heart-to-cell isomorphism restricts translation by the inverse parabolic factor. -/
theorem heartMinimalIso_hom_comp (I : Set G.rootBase.support) (w : G.weylGroup) :
    (heartMinimalIso G I w).hom ≫
        schubertCellInclusion G (leftParabolicRepresentative G.rootBase I w) =
      heartInclusion G I w ≫
        (Variety.translationIso (reductiveVariety G) (flagVariety G)
          (reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)))).inv := by
  apply (cancel_epi (heartTranslationIso G I w).hom).mp
  simp only [heartMinimalIso, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, heartTranslationIso_hom_comp, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end SchubertOrbits
