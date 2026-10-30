import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviSimple
import OrbitComplexity.GroupActions.Actions.Translations

/-! # Root-parameter translations on the simple Schubert chart -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
universe u
variable {K : Type u} [Field K]

private theorem parameter_add {B : Type u} [CommRing B] [HopfAlgebra K B]
    (x : B →ₐc[K] SymmetricAlgebra K K) (a t : K) :
    gaParameterPoint x (a + t) = gaParameterPoint x a * gaParameterPoint x t := by
  change AlgHom.mapDomain x
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd a * Multiplicative.ofAdd t)) = _
  rw [map_mul, map_mul]
  rfl

private theorem additivePoint_add (a t : K) :
    additivePointsEquiv K (a + t) = additivePointsEquiv K a * additivePointsEquiv K t := by
  change affineGroupPointsMulEquiv K (SymmetricAlgebra K K)
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd a * Multiplicative.ofAdd t)) = _
  rw [map_mul, map_mul]
  rfl

private theorem equivariant_smul {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (t : H.points) (q : X.points) :
    Variety.mapPoints f (t • q) = t • Variety.mapPoints f q := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (t • q) ≫ f = Y.pointsEquivOverHom (t • Variety.mapPoints f q)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom t) (X.pointsEquivOverHom q)

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def gaLeviPoint (i : G.rootBase.support) (a : K) : (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨gaParameterPoint (G.simpleRootMap i) a, G.simpleRootPoint_mem_levi {i} i (by simp) a⟩

private theorem gaLeviPoint_coe (i : G.rootBase.support) (a : K) :
    (leviPointsMulEquiv G {i} (gaLeviPoint G i a) : G.points) =
      gaParameterPoint (G.simpleRootMap i) a := by
  simp only [gaLeviPoint, MulEquiv.apply_symm_apply]

private theorem positiveChart_ga_points (i : G.rootBase.support) (a t : K) :
    gaLeviPoint G i a • Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K t) =
      Variety.mapPoints (simplePositiveChart G i) (additivePointsEquiv K (a + t)) := by
  apply Variety.mapPoints_injective_of_mono
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
  rw [equivariant_smul, leviFlag_smul, gaLeviPoint_coe,
    ← Variety.mapPoints_comp, ← Variety.mapPoints_comp,
    simplePositiveChart_points, simplePositiveChart_points, flagVarietyAction_points]
  apply congrArg (flagVarietyPointsEquiv G)
  rw [← flagProjection_smul]
  rw [← mul_assoc, ← parameter_add]

omit [CharZero K] in
private theorem chart_translate {H X : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (f : (additiveVariety K).toOver ⟶ X.toOver)
    (g : H.points) (a : K)
    (h : ∀ t, g • Variety.mapPoints f (additivePointsEquiv K t) =
      Variety.mapPoints f (additivePointsEquiv K (a + t))) :
    f ≫ Variety.translateMorphism H X g =
      (leftTranslation (additiveVariety K) (additivePointsEquiv K a)).hom ≫
        f := by
  apply Variety.mapPoints_injective
  funext q
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective q
  simp only [Variety.mapPoints_comp, Variety.mapPoints_translateMorphism, leftTranslation_points]
  rw [← additivePoint_add]
  exact h t

/-- Left multiplication by the chosen positive root adds its parameter on the open chart. -/
theorem simplePositiveChart_ga (i : G.rootBase.support) (a : K) :
    type_of% (chart_translate (H := leviVariety G {i})
      (X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (simplePositiveChart G i) (gaLeviPoint G i a) a (positiveChart_ga_points G i a)) :=
  chart_translate (H := leviVariety G {i})
    (X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (simplePositiveChart G i) (gaLeviPoint G i a) a (positiveChart_ga_points G i a)

end SchubertGeometry
