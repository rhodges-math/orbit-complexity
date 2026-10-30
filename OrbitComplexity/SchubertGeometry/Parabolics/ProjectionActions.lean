import OrbitComplexity.SchubertGeometry.Parabolics.Stability
import OrbitComplexity.SchubertGeometry.Parabolics.Birational
import OrbitComplexity.SchubertGeometry.Parabolics.LeviStability
import OrbitComplexity.SchubertGeometry.Levi.Reductive
import OrbitComplexity.GroupActions.Rosenlicht.ReductiveComplexity
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.GroupActions.Rosenlicht.RegularEquivariance

/-! # Equivariant partial Schubert projections

The canonical projection preserves Levi actions. Its dense-cell isomorphism identifies
the complexities whenever the same Levi subgroup acts on both Schubert varieties.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
universe u

private theorem map_smul {K : Type u} [Field K] (H X Y : GroupActions.Variety K)
    [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem projection_levi_smul (I J : Set G.rootBase.support)
    (l : (leviVariety G I).points) (x : (flagVariety G).points) :
    Variety.mapPoints (partialFlagMorphism G J) (l • x) =
      l • Variety.mapPoints (partialFlagMorphism G J) x := by
  let : IsModHom (reductiveVariety G).toOver (partialFlagMorphism G J) :=
    partialFlagMorphism_isModHom G J
  calc
    _ = Variety.mapPoints (partialFlagMorphism G J)
        (reductivePointsMulEquiv G (leviPointsMulEquiv G I l) • x) :=
      congrArg _ (leviFlag_smul G I l x)
    _ = reductivePointsMulEquiv G (leviPointsMulEquiv G I l) •
        Variety.mapPoints (partialFlagMorphism G J) x :=
      map_smul (reductiveVariety G) (flagVariety G) (partialFlagVariety G J)
        (partialFlagMorphism G J) _ _
    _ = _ := (leviPartialFlag_smul G I J l
      (Variety.mapPoints (partialFlagMorphism G J) x)).symm

/-- The Schubert projection is equivariant when the Levi acts on both varieties. -/
theorem partialSchubertProjection_isModHom (I J : Set G.rootBase.support)
    (w : G.weylGroup) (hw : IsMinimalRightParabolic G.rootBase J w)
    (hTop : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J))
    (hFull : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) :
  letI := schubertLeviAction G I w hFull
  letI := partialSchubertLeviAction G I J w hw hTop
  IsModHom (leviVariety G I).toOver (partialSchubertProjection G J w) := by
  let := schubertLeviAction G I w hFull
  let := partialSchubertLeviAction G I J w hw hTop
  let : IsModHom (leviVariety G I).toOver (schubertInclusion G w) :=
    schubertLeviEquivariant G I w hFull
  let : IsModHom (leviVariety G I).toOver (partialSchubertInclusion G J w) :=
    partialSchubertLeviEquivariant G I J w hw hTop
  apply Variety.isModHom_of_points (leviVariety G I) (schubertVariety G w)
    (partialSchubertVariety G J w) (partialSchubertProjection G J w)
  intro h x
  have hfac (y : (schubertVariety G w).points) :
      Variety.mapPoints (partialSchubertInclusion G J w)
          (Variety.mapPoints (partialSchubertProjection G J w) y) =
        Variety.mapPoints (partialFlagMorphism G J)
          (Variety.mapPoints (schubertInclusion G w) y) := by
    have hc := congrArg (fun f : (schubertVariety G w).toOver ⟶
      (partialFlagVariety G J).toOver => Variety.mapPoints f y)
        (partialSchubertProjection_comp G J w)
    simpa only [Variety.mapPoints_comp] using hc
  apply Variety.mapPoints_injective_of_mono (partialSchubertInclusion G J w)
  rw [hfac, map_smul (leviVariety G I) (partialSchubertVariety G J w)
      (partialFlagVariety G J) (partialSchubertInclusion G J w), hfac,
    map_smul (leviVariety G I) (schubertVariety G w) (flagVariety G)
      (schubertInclusion G w), projection_levi_smul]

/-- The full and partial Schubert varieties have equal complexity for a common Levi action. -/
theorem partial_schubert_complexity (I J : Set G.rootBase.support)
    (w : G.weylGroup) (hw : IsMinimalRightParabolic G.rootBase J w)
    (hTop : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J))
    (hFull : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) :
  letI := schubertLeviAction G I w hFull
  letI := partialSchubertLeviAction G I J w hw hTop
  letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
      (schubertVariety G w).toOver :=
    inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
  letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
      (partialSchubertVariety G J w).toOver :=
    inferInstanceAs (ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver)
  complexity (leviGroupData G I) (partialSchubertVariety G J w) =
    complexity (leviGroupData G I) (schubertVariety G w) := by
  let := schubertLeviAction G I w hFull
  let := partialSchubertLeviAction G I J w hw hTop
  let : ModObj (reductiveVariety (leviGroupData G I)).toOver
      (schubertVariety G w).toOver :=
    inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
  let : ModObj (reductiveVariety (leviGroupData G I)).toOver
      (partialSchubertVariety G J w).toOver :=
    inferInstanceAs (ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver)
  have hF : IsModHom (leviVariety G I).toOver (partialSchubertProjection G J w) :=
    partialSchubertProjection_isModHom G I J w hw hTop hFull
  let : IsModHom (reductiveVariety (leviGroupData G I)).toOver
      (partialSchubertProjection G J w) := hF
  obtain ⟨p, hp, hcomp⟩ := (partialSchubertProjection_properties G J w).2.2.2 hw
  have heq := Variety.partialIso_rationalEquivariant
    (reductiveVariety (leviGroupData G I)) (schubertVariety G w)
    (partialSchubertVariety G J w) (partialSchubertProjection G J w) p hcomp.symm
  exact (complexity_eq_of_birational (leviGroupData G I) (schubertVariety G w)
    (partialSchubertVariety G J w) p hp heq).symm

end SchubertGeometry
