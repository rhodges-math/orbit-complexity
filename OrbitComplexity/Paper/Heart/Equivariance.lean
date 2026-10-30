import OrbitComplexity.Paper.Heart.Translation
import OrbitComplexity.Paper.Heart.Actions
import OrbitComplexity.Paper.Heart.TwistedActions
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.GroupActions.Actions.EquivariantPoints

/-!
# Equivariance of inverse parabolic translation

Inverse translation intertwines the ordinary action on the heart and the inverse
Weyl twist on the minimal Schubert cell.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits
open ReductiveGroups TauCeti GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Inverse representative conjugation is the twist by the inverse Weyl element. -/
theorem torusConjugation_inverse (a : G.weylGroup) :
    (torusConjugationIso G (G.weylPoint a)⁻¹
      ((Subgroup.normalizer (G.torusPoints : Set G.points)).inv_mem
        (G.weylPoint_mem_normalizer a))).hom =
      (torusConjugationIso G (G.weylPoint a⁻¹) (G.weylPoint_mem_normalizer a⁻¹)).hom := by
  obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.weylElementPoint_inv G.rootBase a
  have he' : (G.weylPoint a)⁻¹ = t * G.weylPoint a⁻¹ := by
    simpa only [G.weylPoint_eq] using he
  let s : G.torusPoints := ⟨(G.weylPoint a⁻¹)⁻¹ * t * G.weylPoint a⁻¹,
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer a⁻¹) t).mp ht⟩
  have hs : (G.weylPoint a)⁻¹ = G.weylPoint a⁻¹ * s := by
    rw [he']
    dsimp only [s]
    group
  have h := torusConjugation_representative G (G.weylPoint a⁻¹)
    (G.weylPoint_mem_normalizer a⁻¹) s
  simpa only [← hs] using h

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points (H X Y : Variety K) [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

/-- The heart-to-cell isomorphism acts on flags by inverse translation. -/
theorem heartMinimalIso_points (I : Set G.rootBase.support) (w : G.weylGroup)
    (x : (heart G I w).points) :
    Variety.mapPoints (schubertCellInclusion G
      (leftParabolicRepresentative G.rootBase I w))
      (Variety.mapPoints (heartMinimalIso G I w).hom x) =
      (reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)))⁻¹ •
        Variety.mapPoints (heartInclusion G I w) x := by
  have h := congrArg (fun f : (heart G I w).toOver ⟶ (flagVariety G).toOver =>
    Variety.mapPoints f x) (heartMinimalIso_hom_comp G I w)
  simpa only [Variety.mapPoints_comp, Variety.translationIso,
    Variety.mapPoints_translateMorphism] using h

private theorem inverse_translate_torus (a : G.weylGroup)
    (t : (torusVariety G).points) (q : (flagVariety G).points) :
    (reductivePointsMulEquiv G (G.weylPoint a))⁻¹ • (t • q) =
      (Variety.mapPoints (torusConjugationIso G (G.weylPoint a⁻¹)
        (G.weylPoint_mem_normalizer a⁻¹)).hom t) •
        ((reductivePointsMulEquiv G (G.weylPoint a))⁻¹ • q) := by
  have hc : Variety.mapPoints (torusInclusion G)
      (Variety.mapPoints (torusConjugationIso G (G.weylPoint a⁻¹)
        (G.weylPoint_mem_normalizer a⁻¹)).hom t) =
      (reductivePointsMulEquiv G (G.weylPoint a))⁻¹ *
        Variety.mapPoints (torusInclusion G) t *
          reductivePointsMulEquiv G (G.weylPoint a) := by
    rw [torusInclusion_points, torusInclusion_points,
      ← torusConjugation_inverse, torusConjugationIso_points, inv_inv]
    change (reductivePointsMulEquiv G)
      ((G.weylPoint a)⁻¹ * (torusPointsMulEquiv G t : G.points) * G.weylPoint a) =
        (reductivePointsMulEquiv G (G.weylPoint a))⁻¹ *
          reductivePointsMulEquiv G (torusPointsMulEquiv G t : G.points) *
            reductivePointsMulEquiv G (G.weylPoint a)
    simp only [map_mul, map_inv]
  rw [Variety.restricted_smul (torusInclusion G),
    Variety.restricted_smul (torusInclusion G), hc]
  simp only [mul_smul, smul_inv_smul]

/-- Inverse parabolic translation intertwines the usual heart action and the inverse Weyl twist. -/
theorem heartMinimalIso_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : (torusVariety G).points) (x : (heart G I w).points) :
    letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
      (schubertCell G (leftParabolicRepresentative G.rootBase I w))
    Variety.mapPoints (heartMinimalIso G I w).hom (t • x) =
      t • Variety.mapPoints (heartMinimalIso G I w).hom x := by
  have hc (s : (torusVariety G).points)
      (y : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
      Variety.mapPoints (schubertCellInclusion G
        (leftParabolicRepresentative G.rootBase I w)) (s • y) =
        s • Variety.mapPoints (schubertCellInclusion G
          (leftParabolicRepresentative G.rootBase I w)) y :=
    equivariant_points _ _ _ _ s y
  rw [twistedAction_smul]
  dsimp only
  apply Variety.mapPoints_injective_of_mono
    (schubertCellInclusion G (leftParabolicRepresentative G.rootBase I w))
  rw [hc, heartMinimalIso_points, heartMinimalIso_points, heart_torus_smul]
  exact inverse_translate_torus G _ t _

/-- The inverse translation is an algebraic torus-equivariant heart isomorphism. -/
theorem heartMinimalIso_isModHom (I : Set G.rootBase.support) (w : G.weylGroup) :
    letI := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
      (schubertCell G (leftParabolicRepresentative G.rootBase I w))
    IsModHom (torusVariety G).toOver (heartMinimalIso G I w).hom := by
  let := twistedAction G (leftParabolicFactor G.rootBase I w)⁻¹
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
  exact Variety.isModHom_of_points (torusVariety G) (heart G I w)
    (schubertCell G (leftParabolicRepresentative G.rootBase I w))
    (heartMinimalIso G I w).hom (heartMinimalIso_smul G I w)

end SchubertOrbits
