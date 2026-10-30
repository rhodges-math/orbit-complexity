import OrbitComplexity.SchubertGeometry.ProjectiveLine.BorelCoordinates

/-! # Rational points in singleton Levi-Borel coordinates -/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

/-- The singleton Levi-Borel coordinates preserve the torus and chosen additive parameters. -/
theorem simpleBorelCoordinates_points (i : G.rootBase.support)
    (p : (Variety.productVariety (torusVariety G) (additiveVariety K)).points) :
    (leviBorelPointsMulEquiv G {i}
      (Variety.mapPoints (simpleBorelCoordinates G i).hom p) : G.points) =
      (torusPointsMulEquiv G (Variety.mapPoints (fst _ _) p) : G.points) *
        gaParameterPoint (G.simpleRootMap i)
          ((additivePointsEquiv K).symm (Variety.mapPoints (snd _ _) p)) := by
  apply (reductivePointsMulEquiv G).injective
  rw [← leviBorelInclusion_points, ← Variety.mapPoints_comp,
    simpleBorelCoordinates_comp, mapPoints_mul, Variety.mapPoints_comp,
    Variety.mapPoints_comp, torusInclusion_points]
  rw [map_mul]
  congr 1
  have he : Variety.mapPoints
      (X := Variety.productVariety (torusVariety G) (additiveVariety K))
      (Y := additiveVariety K) (snd _ _) p =
      additivePointsEquiv K
        ((additivePointsEquiv K).symm (Variety.mapPoints (snd _ _) p)) :=
    ((additivePointsEquiv K).apply_symm_apply _).symm
  rw [he, gaMorphism_points, Equiv.symm_apply_apply]
  rfl

end SchubertGeometry
