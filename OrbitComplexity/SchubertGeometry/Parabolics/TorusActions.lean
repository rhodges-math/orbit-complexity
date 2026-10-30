import OrbitComplexity.SchubertGeometry.Parabolics.ProjectionActions
import OrbitComplexity.SchubertGeometry.Parabolics.EmptyLevi
import OrbitComplexity.GroupActions.Complexity.Toric
import OrbitComplexity.SchubertGeometry.Levi.BorelComparison
import OrbitComplexity.SchubertGeometry.Cells.ActionPoints

/-! # Torus complexity under the partial flag projection

The empty standard Levi subgroup identifies with the chosen torus. Its action restricts
to the partial Schubert variety and transfers complexity from the full Schubert variety.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry
universe u
variable {K : Type u} [Field K]

private theorem map_smul {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f =
    Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def torusLeviMap : (torusVariety G).toOver ⟶ (leviVariety G ∅).toOver :=
  torusLeviBorelInclusion G ∅ ≫ leviBorelLeviInclusion G ∅

private instance torusLeviMap_mon : IsMonHom (torusLeviMap G) := by
  dsimp only [torusLeviMap]
  infer_instance

private theorem torusLeviMap_comp :
    torusLeviMap G ≫ leviInclusion G ∅ = torusInclusion G := by
  rw [torusLeviMap, Category.assoc, leviBorelLeviInclusion_comp,
    torusLeviBorelInclusion_comp]

private theorem empty_complexity (X : Variety K)
    [ModObj (leviVariety G ∅).toOver X.toOver] :
    letI : ModObj (reductiveVariety (leviGroupData G ∅)).toOver X.toOver :=
      inferInstanceAs (ModObj (leviVariety G ∅).toOver X.toOver)
    letI := Mod.scalarRestriction (torusLeviMap G) X.toOver
    torusComplexity G X = complexity (leviGroupData G ∅) X := by
  let : ModObj (reductiveVariety (leviGroupData G ∅)).toOver X.toOver :=
    inferInstanceAs (ModObj (leviVariety G ∅).toOver X.toOver)
  have : IsIso (torusLeviBorelInclusion G ∅) := (emptyLevi_isTorus G).2.2.1
  have : IsIso (torusLeviBorelInclusion G ∅ ≫ leviBorelLeviInclusion G ∅) :=
    (emptyLevi_isTorus G).2.2.2
  have hBLI : IsIso (leviBorelLeviInclusion G ∅) :=
    IsIso.of_isIso_comp_left (torusLeviBorelInclusion G ∅) _
  have : IsIso ((leviBorelIso G ∅).hom ≫ borelInclusion (leviGroupData G ∅)) := by
    rw [leviBorelIso_comp G ∅]
    exact hBLI
  have : IsIso (borelInclusion (leviGroupData G ∅)) :=
    IsIso.of_isIso_comp_left (leviBorelIso G ∅).hom _
  have hB : complexity (leviGroupData G ∅) X =
      minOrbitCodim (leviVariety G ∅) X :=
    Variety.restricted_minOrbitCodim (borelInclusion (leviGroupData G ∅))
      (Variety.pointsHomeomorph (asIso (borelInclusion (leviGroupData G ∅)))).surjective X
  have : IsIso (torusLeviMap G) := (emptyLevi_isTorus G).2.2.2
  exact (Variety.restricted_minOrbitCodim (torusLeviMap G)
    (Variety.pointsHomeomorph (asIso (torusLeviMap G))).surjective X).trans hB.symm

private theorem full_torus_smul (w : G.weylGroup) (t : (torusVariety G).points)
    (x : (schubertVariety G w).points) :
    letI := schubertLeviAction G ∅ w (Set.empty_subset _)
    Variety.mapPoints (torusLeviMap G) t • x = t • x := by
  let := schubertLeviAction G ∅ w (Set.empty_subset _)
  let : IsModHom (leviVariety G ∅).toOver (schubertInclusion G w) :=
    schubertLeviEquivariant G ∅ w (Set.empty_subset _)
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  rw [map_smul (schubertInclusion G w), schubert_torus_smul G w,
    leviFlag_smul G ∅, ← leviInclusion_points G ∅]
  have he : Variety.mapPoints (leviInclusion G ∅)
      (Variety.mapPoints (torusLeviMap G) t) = Variety.mapPoints (torusInclusion G) t := by
    rw [← Variety.mapPoints_comp, torusLeviMap_comp G]
  rw [he]
  exact (Variety.restricted_smul (torusInclusion G) (flagVariety G) t _).symm

private theorem full_empty_complexity (w : G.weylGroup) :
    letI := schubertLeviAction G ∅ w (Set.empty_subset _)
    letI : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G ∅).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G ∅) (schubertVariety G w) =
      torusComplexity G (schubertVariety G w) := by
  let ordinary := torusComplexity G (schubertVariety G w)
  let ordinaryOrbit := fun x : (schubertVariety G w).points =>
    MulAction.orbit (torusVariety G).points x
  let := schubertLeviAction G ∅ w (Set.empty_subset _)
  let : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
      (schubertVariety G w).toOver :=
    inferInstanceAs (ModObj (leviVariety G ∅).toOver (schubertVariety G w).toOver)
  have horbit (x : (schubertVariety G w).points) :
      letI := Mod.scalarRestriction (torusLeviMap G) (schubertVariety G w).toOver
      MulAction.orbit (torusVariety G).points x = ordinaryOrbit x := by
    let := Mod.scalarRestriction (torusLeviMap G) (schubertVariety G w).toOver
    change Set.range (fun t : (torusVariety G).points => t • x) =
      Set.range (fun t : (torusVariety G).points => _)
    congr 1
    funext t
    exact (Variety.restricted_smul (torusLeviMap G) (schubertVariety G w) t x).trans
      (full_torus_smul G w t x)
  have hmin :
      letI := Mod.scalarRestriction (torusLeviMap G) (schubertVariety G w).toOver
      torusComplexity G (schubertVariety G w) = ordinary := by
    let := Mod.scalarRestriction (torusLeviMap G) (schubertVariety G w).toOver
    unfold torusComplexity minOrbitCodim orbitCodim orbitNatDim orbitDim
    simp only [horbit]
    rfl
  exact (empty_complexity G (schubertVariety G w)).symm.trans hmin


/-- The torus action obtained from the empty standard Levi subgroup. -/
@[instance_reducible]
def partialSchubertTorusAction (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    ModObj (torusVariety G).toOver (partialSchubertVariety G J w).toOver :=
  letI := partialSchubertLeviAction G ∅ J w hw (Set.empty_subset _)
  Mod.scalarRestriction (torusLeviBorelInclusion G ∅ ≫ leviBorelLeviInclusion G ∅)
    (partialSchubertVariety G J w).toOver

/-- The torus action on a partial Schubert variety is induced from the partial flag action. -/
theorem partialSchubertTorusEquivariant (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
  letI := Mod.scalarRestriction (torusInclusion G) (partialFlagVariety G J).toOver
  letI := partialSchubertTorusAction G J w hw
  IsModHom (torusVariety G).toOver (partialSchubertInclusion G J w) := by
  let := partialSchubertLeviAction G ∅ J w hw (Set.empty_subset _)
  let : IsModHom (leviVariety G ∅).toOver (partialSchubertInclusion G J w) :=
    partialSchubertLeviEquivariant G ∅ J w hw (Set.empty_subset _)
  let := Mod.scalarRestriction (torusInclusion G) (partialFlagVariety G J).toOver
  let := partialSchubertTorusAction G J w hw
  apply Variety.isModHom_of_points (torusVariety G) (partialSchubertVariety G J w)
    (partialFlagVariety G J) (partialSchubertInclusion G J w)
  intro t x
  have he : Variety.mapPoints (leviInclusion G ∅)
      (Variety.mapPoints (torusLeviMap G) t) = Variety.mapPoints (torusInclusion G) t := by
    rw [← Variety.mapPoints_comp, torusLeviMap_comp G]
  calc
    _ = Variety.mapPoints (partialSchubertInclusion G J w)
        (Variety.mapPoints (torusLeviMap G) t • x) :=
      congrArg _ (Variety.restricted_smul (torusLeviMap G)
        (partialSchubertVariety G J w) t x)
    _ = Variety.mapPoints (torusLeviMap G) t •
        Variety.mapPoints (partialSchubertInclusion G J w) x :=
      map_smul (partialSchubertInclusion G J w) _ x
    _ = Variety.mapPoints (leviInclusion G ∅)
          (Variety.mapPoints (torusLeviMap G) t) •
        Variety.mapPoints (partialSchubertInclusion G J w) x :=
      Variety.restricted_smul (leviInclusion G ∅) (partialFlagVariety G J) _ _
    _ = _ := by
      rw [he]
      exact (Variety.restricted_smul (torusInclusion G) (partialFlagVariety G J) t _).symm

/-- Partial and full Schubert varieties have equal torus complexity. -/
theorem partial_torus_complexity (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
  letI := partialSchubertTorusAction G J w hw
  torusComplexity G (partialSchubertVariety G J w) =
    torusComplexity G (schubertVariety G w) := by
  let := partialSchubertLeviAction G ∅ J w hw (Set.empty_subset _)
  let := schubertLeviAction G ∅ w (Set.empty_subset _)
  let : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
      (partialSchubertVariety G J w).toOver :=
    inferInstanceAs (ModObj (leviVariety G ∅).toOver (partialSchubertVariety G J w).toOver)
  let : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
      (schubertVariety G w).toOver :=
    inferInstanceAs (ModObj (leviVariety G ∅).toOver (schubertVariety G w).toOver)
  exact (empty_complexity G (partialSchubertVariety G J w)).trans
    ((partial_schubert_complexity G ∅ J w hw (Set.empty_subset _)
      (Set.empty_subset _)).trans (full_empty_complexity G w))

end SchubertGeometry
