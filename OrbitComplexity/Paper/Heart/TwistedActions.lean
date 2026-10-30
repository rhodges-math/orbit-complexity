import OrbitComplexity.GroupActions.Tori.Conjugation
import OrbitComplexity.GroupActions.Actions.RestrictionOrbits
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRoots

/-!
# Twisted torus actions

Conjugating the torus by a normalizer representative twists any algebraic torus action.
Right torus factors do not change the conjugation morphism, and the twisted action has
exactly the original orbits.

## Main definitions

* `SchubertOrbits.twistedAction`: the action twisted by a Weyl element.

## Main results

* `SchubertOrbits.twistedAction_properties`: the action formula, representative independence,
  orbit equality and open dense orbit equivalence.

## References

* Y. Gao, R. Hodges, A. Yong, *Levi-spherical Schubert varieties*, Advances in Mathematics
  439 (2024), 109486, arXiv:2305.00555v2, Lemmas 3.1 and 3.2.
-/

noncomputable section

namespace SchubertOrbits

open ReductiveGroups TauCeti GroupActions CategoryTheory

universe u

variable {K : Type u} [Field K] (G : ReductiveGroupData K)

private theorem torus_mul_comm (s t : G.torusPoints) : s * t = t * s := by
  have hco : Coalgebra.IsCocomm K (CommHopfAlgCat.quotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal) :=
    G.torus_isTorus.isCocomm K G.torusAlgebra
  have hcomm : IsMulCommutative G.torusPoints :=
    @CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup K _
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal hco (CommAlgCat.of K K)
  exact @mul_comm' G.torusPoints _ hcomm s t

/-- Conjugation on the torus is independent of a right torus factor in the representative. -/
theorem conjugation_torus_factor (g : G.points) (s t : G.torusPoints) :
    (g * s) * t * (g * s)⁻¹ = g * t * g⁻¹ := by
  have hst : (s : G.points) * (t : G.points) = (t : G.points) * (s : G.points) :=
    congrArg Subtype.val (torus_mul_comm G s t)
  rw [mul_inv_rev]
  calc
    g * s * t * (s⁻¹ * g⁻¹) = g * (s * t) * (s⁻¹ * g⁻¹) := by simp only [mul_assoc]
    _ = g * (t * s) * (s⁻¹ * g⁻¹) := by rw [hst]
    _ = g * t * g⁻¹ := by
      simp only [Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]

variable [IsAlgClosed K]

/-- A right torus factor in a normalizer representative does not change the torus morphism. -/
theorem torusConjugation_representative (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) (s : G.torusPoints) :
    (torusConjugationIso G (g * s)
      (Subgroup.mul_mem _ hg (G.torusPoints.le_normalizer s.property))).hom =
      (torusConjugationIso G g hg).hom := by
  apply Variety.mapPoints_injective
  funext t
  apply (torusPointsMulEquiv G).injective
  apply Subtype.ext
  rw [torusConjugationIso_points, torusConjugationIso_points]
  exact conjugation_torus_factor G g s (torusPointsMulEquiv G t)

variable [CharZero K]

/-- The torus action twisted by a Weyl element through its normalizer representative. -/
@[instance_reducible]
def twistedAction (u : G.weylGroup) (X : Variety K)
    [ModObj (torusVariety G).toOver X.toOver] : ModObj (torusVariety G).toOver X.toOver :=
  Mod.scalarRestriction
    (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom X.toOver

/-- The twisted action has the usual action after the torus conjugation automorphism. -/
theorem twistedAction_smul (u : G.weylGroup) (X : Variety K)
    [ModObj (torusVariety G).toOver X.toOver] (t : (torusVariety G).points) (x : X.points) :
    let ordinarySmul : (torusVariety G).points → X.points → X.points := (· • ·)
    letI := twistedAction G u X
    t • x = ordinarySmul (Variety.mapPoints
      (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom t) x := by
  exact Variety.restricted_smul _ X t x

/-- Twisting the torus action by a Weyl element preserves every orbit. -/
theorem twistedAction_orbit (u : G.weylGroup) (X : Variety K)
    [ModObj (torusVariety G).toOver X.toOver] (x : X.points) :
    let ordinaryOrbit := MulAction.orbit (torusVariety G).points x
    letI := twistedAction G u X
    MulAction.orbit (torusVariety G).points x = ordinaryOrbit := by
  exact Variety.restricted_orbit _
    (Variety.pointsHomeomorph
      (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u))).surjective X x

/-- The usual and Weyl-twisted torus actions have an open dense orbit simultaneously. -/
theorem twistedAction_open_dense (u : G.weylGroup) (X : Variety K)
    [ModObj (torusVariety G).toOver X.toOver] :
    let ordinaryOpenDense := ∃ x : X.points,
      IsOpen (MulAction.orbit (torusVariety G).points x) ∧
        Dense (MulAction.orbit (torusVariety G).points x)
    letI := twistedAction G u X
    (∃ x : X.points, IsOpen (MulAction.orbit (torusVariety G).points x) ∧
      Dense (MulAction.orbit (torusVariety G).points x)) ↔ ordinaryOpenDense := by
  simp only [twistedAction_orbit]

/-- Weyl twists give a representative-independent torus action with the original orbits. -/
theorem twistedAction_properties (u : G.weylGroup) (X : Variety K)
    [ModObj (torusVariety G).toOver X.toOver] :
    (∀ s : G.torusPoints,
      (torusConjugationIso G (G.weylPoint u * s)
        (Subgroup.mul_mem _ (G.weylPoint_mem_normalizer u)
          (G.torusPoints.le_normalizer s.property))).hom =
        (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom) ∧
    (∀ (t : (torusVariety G).points) (x : X.points),
      let ordinarySmul : (torusVariety G).points → X.points → X.points := (· • ·)
      letI := twistedAction G u X
      t • x = ordinarySmul (Variety.mapPoints
        (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom t) x) ∧
    (∀ x : X.points,
      let ordinaryOrbit := MulAction.orbit (torusVariety G).points x
      letI := twistedAction G u X
      MulAction.orbit (torusVariety G).points x = ordinaryOrbit) ∧
    (let ordinaryOpenDense := (∃ x : X.points,
       IsOpen (MulAction.orbit (torusVariety G).points x) ∧
         Dense (MulAction.orbit (torusVariety G).points x));
      letI := twistedAction G u X;
      (∃ x : X.points, IsOpen (MulAction.orbit (torusVariety G).points x) ∧
        Dense (MulAction.orbit (torusVariety G).points x)) ↔ ordinaryOpenDense) :=
  ⟨fun s => torusConjugation_representative G _ (G.weylPoint_mem_normalizer u) s,
    fun t x => twistedAction_smul G u X t x, fun x => twistedAction_orbit G u X x,
    twistedAction_open_dense G u X⟩

end SchubertOrbits
