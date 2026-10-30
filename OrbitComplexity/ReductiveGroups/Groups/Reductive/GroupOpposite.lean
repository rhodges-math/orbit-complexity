import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupUnipotent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-!
# The opposite Borel and its unipotent subgroup

Conjugation by the representative of the longest Weyl element defines the
opposite Borel subgroup and its unipotent subgroup. Their coordinate algebras
are quotients by the conjugated Hopf ideals.

## Main definitions

* `ReductiveGroups.ReductiveGroupData.oppositeBorelIdeal`: the opposite Borel ideal.
* `ReductiveGroups.ReductiveGroupData.oppositeUnipotentIdeal`: its unipotent subgroup ideal.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti CategoryTheory

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The defining Hopf ideal of the Borel subgroup opposite to the chosen Borel. -/
def oppositeBorelIdeal : HopfIdeal K G.coordinateAlgebra :=
  G.borelIdeal.conjugate G.longestPoint

/-- The defining Hopf ideal of the opposite root-unipotent subgroup. -/
def oppositeUnipotentIdeal : HopfIdeal K G.coordinateAlgebra :=
  G.unipotentIdeal.conjugate G.longestPoint

/-- The group of rational points of the opposite Borel subgroup. -/
def oppositeBorelPoints : Subgroup G.points :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
    G.oppositeBorelIdeal (CommAlgCat.of K K)

/-- The group of rational points of the opposite root-unipotent subgroup. -/
def oppositeUnipotentPoints : Subgroup G.points :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
    G.oppositeUnipotentIdeal (CommAlgCat.of K K)

/-- The opposite Borel ideal cuts out a Borel subgroup. -/
theorem oppositeBorel_isBorel :
    HopfIdeal.IsBorel K (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal :=
  G.isBorel.conjugate G.longestPoint

/-- The finite type coordinate Hopf algebra of the opposite Borel subgroup. -/
def oppositeBorelAlgebra : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra G.oppositeBorelIdeal

/-- The finite type coordinate Hopf algebra of the opposite unipotent subgroup. -/
def oppositeUnipotentAlgebra : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra G.oppositeUnipotentIdeal

/-- Conjugation identifies the opposite unipotent coordinate algebra with the unipotent algebra. -/
def oppositeUnipotentIso : G.oppositeUnipotentAlgebra ≅ G.unipotentAlgebra := by
  change FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra
      (G.unipotentIdeal.conjugate G.longestPoint) ≅ _
  rw [HopfIdeal.conjugate_eq_comapOfSurjective]
  let e : G.coordinateAlgebra ≅ G.coordinateAlgebra := ObjectProperty.isoMk _ <|
    (CommHopfAlgCat.ofIsoSelf G.coordinateAlgebra.obj).symm ≪≫
      CommHopfAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv G.longestPoint) ≪≫
      CommHopfAlgCat.ofIsoSelf G.coordinateAlgebra.obj
  have he : FiniteTypeCommHopfAlgCat.toBialgHom e.hom =
      (HopfAlgebra.pointConjugationBialgEquiv G.longestPoint).toBialgHom := by
    ext a
    rfl
  simpa only [he, unipotentAlgebra] using
    FiniteTypeCommHopfAlgCat.quotientIsoOfIso e G.unipotentIdeal

private def oppositeUnipotentHopfIso :
    G.oppositeUnipotentAlgebra.obj ≅ G.unipotentAlgebra.obj :=
  (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} K) (CommHopfAlgCat.{u} K)).mapIso
    G.oppositeUnipotentIso

/-- The opposite unipotent coordinate quotient is smooth. -/
theorem oppositeUnipotent_smooth :
    smoothCommHopfAlgProperty K G.oppositeUnipotentAlgebra.obj :=
  (smoothCommHopfAlgProperty K).prop_of_iso G.oppositeUnipotentHopfIso.symm G.unipotent_smooth

/-- The opposite unipotent coordinate quotient is geometrically connected. -/
theorem oppositeUnipotent_geometricallyConnected :
    geometricallyConnectedCommHopfAlgProperty K G.oppositeUnipotentAlgebra.obj :=
  (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso
    G.oppositeUnipotentHopfIso.symm G.unipotent_geometricallyConnected

/-- The opposite root-unipotent quotient is geometrically unipotent. -/
theorem oppositeUnipotent_geometricallyUnipotent :
    geometricallyUnipotentPointsCommHopfAlgProperty K G.oppositeUnipotentAlgebra.obj :=
  (geometricallyUnipotentPointsCommHopfAlgProperty K).prop_of_iso
    G.oppositeUnipotentHopfIso.symm G.unipotent_geometricallyUnipotent

/-- The opposite Borel coordinate quotient is smooth. -/
theorem oppositeBorel_smooth : smoothCommHopfAlgProperty K G.oppositeBorelAlgebra.obj :=
  borelQuotient_smooth G.oppositeBorelIdeal G.oppositeBorel_isBorel

/-- The opposite Borel coordinate quotient is geometrically connected. -/
theorem oppositeBorel_geometricallyConnected :
    geometricallyConnectedCommHopfAlgProperty K G.oppositeBorelAlgebra.obj :=
  borelQuotient_geometricallyConnected G.oppositeBorelIdeal G.oppositeBorel_isBorel

/-- The opposite unipotent rational points form a subgroup of the opposite Borel points. -/
theorem oppositeUnipotent_le_oppositeBorel : G.oppositeUnipotentPoints ≤ G.oppositeBorelPoints :=
  CommHopfAlgCat.quotientPointsSubgroup_le_of_le _
    (HopfIdeal.conjugate_mono G.longestPoint G.borel_le_unipotentIdeal) _

/-- Conjugation by the longest representative identifies Borel and opposite Borel points. -/
theorem conj_mem_oppositeBorel (x : G.points) :
    G.longestPoint * x * G.longestPoint⁻¹ ∈ G.oppositeBorelPoints ↔ x ∈ G.borelPoints := by
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
    AlgHom.mapValue_id, MonoidHom.id_apply, oppositeBorelPoints, oppositeBorelIdeal,
    borelPoints] using
    CommHopfAlgCat.pointConjugation_mem_conjugate_iff G.borelIdeal G.longestPoint
      (CommAlgCat.of K K) x

/-- Conjugation by the longest representative identifies unipotent and opposite points. -/
theorem conj_mem_oppositeUnipotent (x : G.points) :
    G.longestPoint * x * G.longestPoint⁻¹ ∈ G.oppositeUnipotentPoints ↔
      x ∈ G.unipotentPoints := by
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
    AlgHom.mapValue_id, MonoidHom.id_apply, oppositeUnipotentPoints, oppositeUnipotentIdeal,
    unipotentPoints] using
    CommHopfAlgCat.pointConjugation_mem_conjugate_iff G.unipotentIdeal G.longestPoint
      (CommAlgCat.of K K) x

/-- The maximal torus is contained in the opposite Borel subgroup on rational points. -/
theorem torus_le_oppositeBorel : G.torusPoints ≤ G.oppositeBorelPoints := by
  intro t ht
  have hconj : G.longestPoint⁻¹ * t * G.longestPoint ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp G.longestPoint_mem_normalizer t).mp ht
  have hmem := (G.conj_mem_oppositeBorel _).mpr (G.torus_le_borel hconj)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hmem

/-- The opposite Borel defining ideal is contained in the maximal torus ideal. -/
theorem oppositeBorel_le_torus : G.oppositeBorelIdeal ≤ G.torusIdeal := by
  let : IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
      G.torusIdeal) := G.torusAlgebra_isReduced
  exact HopfIdeal.le_of_quotientPointsSubgroup_le (K := K) G.torus_le_oppositeBorel

end ReductiveGroupData
