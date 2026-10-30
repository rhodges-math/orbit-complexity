import OrbitComplexity.Paper.Heart.Isomorphism
import OrbitComplexity.GroupActions.Actions.OrbitIso
import OrbitComplexity.GroupActions.Actions.RestrictionQuotient

/-!
# Torus orbits under parabolic translation

Parabolic translation identifies the ordinary torus orbit quotients of the
minimal Schubert cell and the heart, and preserves every orbit codimension.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Inverse parabolic translation preserves the codimension of each ordinary torus orbit. -/
theorem heart_orbitCodim (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (heart G I w).points) :
    orbitCodim (torusVariety G) (heart G I w) x =
      orbitCodim (torusVariety G)
        (schubertCell G (leftParabolicRepresentative G.rootBase I w))
        (Variety.mapPoints (heartMinimalIso G I w).hom x) := by
  have hiso :
      (letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
        (schubertCell G (leftParabolicRepresentative G.rootBase I w))
       orbitCodim (torusVariety G)
         (schubertCell G (leftParabolicRepresentative G.rootBase I w))
         (Variety.mapPoints (heartMinimalIso G I w).hom x)) =
        orbitCodim (torusVariety G) (heart G I w) x := by
    let := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
      (schubertCell G (leftParabolicRepresentative G.rootBase I w))
    let := heartMinimalIso_isModHom G I w
    exact orbitCodim_iso (torusVariety G) (heartMinimalIso G I w) x
  have htwist := Variety.restricted_orbitCodim
    (torusConjugationIso G (G.weylPoint (leftParabolicFactor G.rootBase I w)⁻¹)
      (G.weylPoint_mem_normalizer _)).hom
    (Variety.pointsHomeomorph
      (torusConjugationIso G (G.weylPoint (leftParabolicFactor G.rootBase I w)⁻¹)
        (G.weylPoint_mem_normalizer _))).surjective
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
    (Variety.mapPoints (heartMinimalIso G I w).hom x)
  exact hiso.symm.trans htwist

/-- The minimum torus orbit codimension of the heart equals that of the minimal Schubert cell. -/
theorem heart_minOrbitCodim (I : Set G.rootBase.support) (w : G.weylGroup) :
    minOrbitCodim (torusVariety G) (heart G I w) =
      minOrbitCodim (torusVariety G)
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) := by
  have hiso :
      (letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
        (schubertCell G (leftParabolicRepresentative G.rootBase I w))
       minOrbitCodim (torusVariety G)
         (schubertCell G (leftParabolicRepresentative G.rootBase I w))) =
        minOrbitCodim (torusVariety G) (heart G I w) := by
    let := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
      (schubertCell G (leftParabolicRepresentative G.rootBase I w))
    let := heartMinimalIso_isModHom G I w
    exact minOrbitCodim_iso (torusVariety G) (heartMinimalIso G I w)
  have htwist := Variety.restricted_minOrbitCodim
    (torusConjugationIso G (G.weylPoint (leftParabolicFactor G.rootBase I w)⁻¹)
      (G.weylPoint_mem_normalizer _)).hom
    (Variety.pointsHomeomorph
      (torusConjugationIso G (G.weylPoint (leftParabolicFactor G.rootBase I w)⁻¹)
        (G.weylPoint_mem_normalizer _))).surjective
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
  exact hiso.symm.trans htwist

private def heartToCellOrbitEquiv (I : Set G.rootBase.support) (w : G.weylGroup) :
    MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points ≃
      MulAction.orbitRel.Quotient (torusVariety G).points
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points := by
  let f := (torusConjugationIso G (G.weylPoint (leftParabolicFactor G.rootBase I w)⁻¹)
    (G.weylPoint_mem_normalizer _)).hom
  let es := Variety.restrictionQuotientEquiv f
    (Variety.pointsHomeomorph
      (torusConjugationIso G (G.weylPoint (leftParabolicFactor G.rootBase I w)⁻¹)
        (G.weylPoint_mem_normalizer _))).surjective
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
  letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
  letI := heartMinimalIso_isModHom G I w
  exact (orbitQuotientEquiv (torusVariety G) (heartMinimalIso G I w)).trans es.symm

/-- Parabolic translation identifies ordinary torus orbits of the minimal cell and the heart. -/
def cellHeartOrbitEquiv (I : Set G.rootBase.support) (w : G.weylGroup) :
    MulAction.orbitRel.Quotient (torusVariety G).points
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points ≃
      MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points :=
  (heartToCellOrbitEquiv G I w).symm

/-- The cell-to-heart orbit equivalence sends a point to its parabolic translate. -/
theorem cellHeartOrbitEquiv_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
    cellHeartOrbitEquiv G I w ⟦x⟧ =
      ⟦Variety.mapPoints (heartTranslationIso G I w).hom x⟧ := rfl

/-- On flags, the cell-to-heart isomorphism is left multiplication by the parabolic factor. -/
theorem heartTranslationIso_points (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
    Variety.mapPoints (heartInclusion G I w)
      (Variety.mapPoints (heartTranslationIso G I w).hom x) =
      reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)) •
        Variety.mapPoints (schubertCellInclusion G
          (leftParabolicRepresentative G.rootBase I w)) x := by
  have h := congrArg (fun f :
      (schubertCell G (leftParabolicRepresentative G.rootBase I w)).toOver ⟶
        (flagVariety G).toOver => Variety.mapPoints f x)
    (heartTranslationIso_hom_comp G I w)
  simpa only [Variety.mapPoints_comp, Variety.translationIso,
    Variety.mapPoints_translateMorphism] using h

/-- The cell-to-heart torus orbit equivalence preserves integer codimension. -/
theorem cellHeartOrbitCodim (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
    orbitCodim (torusVariety G) (heart G I w)
        (Variety.mapPoints (heartTranslationIso G I w).hom x) =
      orbitCodim (torusVariety G)
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) x := by
  rw [heart_orbitCodim]
  change orbitCodim (torusVariety G)
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
      (Variety.mapPoints (heartTranslationIso G I w).inv
        (Variety.mapPoints (heartTranslationIso G I w).hom x)) = _
  rw [← Variety.mapPoints_comp, Iso.hom_inv_id, Variety.mapPoints_id]

end SchubertOrbits
