import OrbitComplexity.GroupActions.Representations.ChevalleyOrbit
import OrbitComplexity.GroupActions.Actions.OrbitVariety
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.SchubertGeometry.Parabolics.PartialPoints

/-! # Standard partial flag varieties

A closed standard parabolic subgroup is the stabilizer of a point in an algebraic
projective action. Its locally closed orbit gives a variety with the prescribed coset
points, a surjective orbit morphism and the left algebraic group action.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact TauCeti.isReduced_of_smooth K G.coordinateAlgebra
attribute [local instance] coordinateReduced

private abbrev LineData := Σ n : ℕ,
  ModObj (reductiveVariety G).toOver
      (projectiveVariety K (ULift.{u} (Fin n))).toOver ×
    (projectiveVariety K (ULift.{u} (Fin n))).points

private theorem line_exists (J : Set G.rootBase.support) :
    ∃ d : LineData G, letI := d.2.1
      ∀ g : G.points, reductivePointsMulEquiv G g • d.2.2 = d.2.2 ↔
        g ∈ SchubertGeometry.standardParabolicPoints G J := by
  obtain ⟨n, μ, p, hp⟩ := exists_projective_stabilizer
    (SchubertGeometry.standardParabolicPoints G J)
    (SchubertGeometry.standardParabolicPoints_bruhat G J).2
  exact ⟨⟨n, μ, p⟩, hp⟩

private def lineData (J : Set G.rootBase.support) : LineData G :=
  Classical.choose (line_exists G J)

private theorem lineData_spec (J : Set G.rootBase.support) :
    letI := (lineData G J).2.1
    ∀ g : G.points, reductivePointsMulEquiv G g • (lineData G J).2.2 =
        (lineData G J).2.2 ↔ g ∈ SchubertGeometry.standardParabolicPoints G J :=
  Classical.choose_spec (line_exists G J)

private abbrev lineSpace (J : Set G.rootBase.support) : GroupActions.Variety K :=
  projectiveVariety K (ULift.{u} (Fin (lineData G J).1))

@[instance_reducible]
private def lineAction (J : Set G.rootBase.support) :
    ModObj (reductiveVariety G).toOver (lineSpace G J).toOver := (lineData G J).2.1
attribute [local instance] lineAction

private abbrev linePoint (J : Set G.rootBase.support) : (lineSpace G J).points :=
  (lineData G J).2.2

/-- The standard partial flag variety as a locally closed orbit in projective space. -/
def partialFlagVariety (J : Set G.rootBase.support) : GroupActions.Variety K :=
  orbitVariety (reductiveVariety G) (lineSpace G J) (linePoint G J)

/-- The orbit morphism from the group to the standard partial flag variety. -/
def partialFlagQuotient (J : Set G.rootBase.support) :
    (reductiveVariety G).toOver ⟶ (partialFlagVariety G J).toOver :=
  orbitProjection (reductiveVariety G) (lineSpace G J) (linePoint G J)

private def inclusion (J : Set G.rootBase.support) :
    (partialFlagVariety G J).toOver ⟶ (lineSpace G J).toOver :=
  orbitInclusion (reductiveVariety G) (lineSpace G J) (linePoint G J)

private instance inclusion_preimmersion (J : Set G.rootBase.support) :
    IsPreimmersion (inclusion G J).left :=
  inferInstanceAs (IsPreimmersion (orbitInclusion (reductiveVariety G)
    (lineSpace G J) (linePoint G J)).left)

private theorem inclusion_fac (J : Set G.rootBase.support) :
    partialFlagQuotient G J ≫ inclusion G J =
      Variety.orbitMorphism (reductiveVariety G) (lineSpace G J) (linePoint G J) :=
  orbitProjection_fac (reductiveVariety G) (lineSpace G J) (linePoint G J)

/-- The orbit morphism is surjective on scheme points. -/
instance partialFlagQuotient_surjective (J : Set G.rootBase.support) :
    Surjective (partialFlagQuotient G J).left :=
  orbitProjection_surjective (reductiveVariety G) (lineSpace G J) (linePoint G J)

private theorem inclusion_points (J : Set G.rootBase.support)
    (g : (reductiveVariety G).points) :
    Variety.mapPoints (inclusion G J) (Variety.mapPoints (partialFlagQuotient G J) g) =
      g • linePoint G J := by
  rw [← Variety.mapPoints_comp, inclusion_fac, Variety.mapPoints_orbitMorphism]

private theorem quotientPoint_eq (J : Set G.rootBase.support) (g h : G.points) :
    Variety.mapPoints (partialFlagQuotient G J) (reductivePointsMulEquiv G g) =
        Variety.mapPoints (partialFlagQuotient G J) (reductivePointsMulEquiv G h) ↔
      g⁻¹ * h ∈ SchubertGeometry.standardParabolicPoints G J := by
  have hi := Variety.mapPoints_injective_of_mono (inclusion G J)
  refine hi.eq_iff.symm.trans ?_
  rw [inclusion_points, inclusion_points]
  calc
    (reductivePointsMulEquiv G g • linePoint G J =
        reductivePointsMulEquiv G h • linePoint G J) ↔
        reductivePointsMulEquiv G (g⁻¹ * h) • linePoint G J = linePoint G J := by
      rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff]
      exact eq_comm
    _ ↔ g⁻¹ * h ∈ SchubertGeometry.standardParabolicPoints G J :=
      lineData_spec G J (g⁻¹ * h)

private def quotientPointMap (J : Set G.rootBase.support) :
    SchubertGeometry.partialFlagPoints G J → (partialFlagVariety G J).points :=
  Quotient.lift (fun g => Variety.mapPoints (partialFlagQuotient G J)
    (reductivePointsMulEquiv G g)) (by
      intro g h hh
      exact (quotientPoint_eq G J g h).mpr (QuotientGroup.leftRel_apply.mp hh))

private theorem quotientPoint_injective (J : Set G.rootBase.support) :
    Function.Injective (quotientPointMap G J) := by
  intro p q he
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  apply QuotientGroup.eq.mpr
  exact (quotientPoint_eq G J g h).mp he

private theorem quotientPoint_surjective (J : Set G.rootBase.support) :
    Function.Surjective (quotientPointMap G J) := by
  intro p
  obtain ⟨x, hx⟩ := orbitProjection_points_surjective
    (reductiveVariety G) (lineSpace G J) (linePoint G J) p
  obtain ⟨g, hg⟩ := (reductivePointsMulEquiv G).surjective x
  refine ⟨QuotientGroup.mk g, ?_⟩
  exact (congrArg (Variety.mapPoints (partialFlagQuotient G J)) hg).trans hx

/-- Standard parabolic cosets identify with rational points of the partial flag variety. -/
def partialFlagPointsEquiv (J : Set G.rootBase.support) :
    SchubertGeometry.partialFlagPoints G J ≃ (partialFlagVariety G J).points :=
  Equiv.ofBijective (quotientPointMap G J)
    ⟨quotientPoint_injective G J, quotientPoint_surjective G J⟩

/-- The orbit morphism sends a group point to its standard parabolic coset. -/
theorem partialFlagQuotient_points (J : Set G.rootBase.support) (g : G.points) :
    Variety.mapPoints (partialFlagQuotient G J) (reductivePointsMulEquiv G g) =
      partialFlagPointsEquiv G J (QuotientGroup.mk g) := rfl

/-- The partial flag variety admits an immersion into finite projective space. -/
theorem partialFlag_quasiprojective (J : Set G.rootBase.support) :
    ∃ n : ℕ, ∃ i : (partialFlagVariety G J).toOver ⟶
      (projectiveVariety K (ULift.{u} (Fin n))).toOver, IsImmersion i.left := by
  refine ⟨(lineData G J).1, inclusion G J, ?_⟩
  refine { __ := inclusion_preimmersion G J, isLocallyClosed_range := ?_ }
  change IsLocallyClosed (Set.range ((orbitInclusion (reductiveVariety G)
    (lineSpace G J) (linePoint G J)).left : _ → _))
  rw [orbitInclusion_range]
  exact orbitImage_locallyClosed (reductiveVariety G) (lineSpace G J) (linePoint G J)

private theorem invariantImage (J : Set G.rootBase.support)
    (h : (reductiveVariety G).points) (y : (partialFlagVariety G J).points) :
    h • Variety.mapPoints (inclusion G J) y ∈ Set.range (Variety.mapPoints (inclusion G J)) := by
  obtain ⟨g, hg⟩ := orbitProjection_points_surjective
    (reductiveVariety G) (lineSpace G J) (linePoint G J) y
  change Variety.mapPoints (partialFlagQuotient G J) g = y at hg
  rw [← hg]
  refine ⟨Variety.mapPoints (partialFlagQuotient G J) (h * g), ?_⟩
  rw [inclusion_points, inclusion_points, mul_smul]

/-- Left translation induces an algebraic action on the partial flag variety. -/
@[instance_reducible]
def partialFlagAction (J : Set G.rootBase.support) :
    ModObj (reductiveVariety G).toOver (partialFlagVariety G J).toOver :=
  Variety.modObjOfInvariant (reductiveVariety G) (lineSpace G J)
    (partialFlagVariety G J) (inclusion G J) (invariantImage G J)
attribute [instance] partialFlagAction

/-- The algebraic action on partial flags agrees with left translation on parabolic cosets. -/
theorem partialFlag_smul (J : Set G.rootBase.support) (g : G.points)
    (p : SchubertGeometry.partialFlagPoints G J) :
    reductivePointsMulEquiv G g • partialFlagPointsEquiv G J p =
      partialFlagPointsEquiv G J (g • p) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective p
  change reductivePointsMulEquiv G g •
      partialFlagPointsEquiv G J (QuotientGroup.mk h) =
    partialFlagPointsEquiv G J (QuotientGroup.mk (g * h))
  apply Variety.mapPoints_injective_of_mono (inclusion G J)
  rw [show Variety.mapPoints (inclusion G J)
        (reductivePointsMulEquiv G g • partialFlagPointsEquiv G J (QuotientGroup.mk h)) =
      reductivePointsMulEquiv G g • Variety.mapPoints (inclusion G J)
        (partialFlagPointsEquiv G J (QuotientGroup.mk h)) from
    Variety.modObjOfInvariant_smul (reductiveVariety G) (lineSpace G J)
      (partialFlagVariety G J) (inclusion G J) (invariantImage G J) _ _]
  rw [← partialFlagQuotient_points, ← partialFlagQuotient_points,
    inclusion_points, inclusion_points, map_mul, mul_smul]

end SchubertGeometry
