import OrbitComplexity.SchubertGeometry.LineBundles.Characters.GaCharacter
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositiveCharacter
import OrbitComplexity.SchubertGeometry.Normality.SchubertBorelCharacter
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots

/-! # The character on the two factors of the rank-one Borel overlap -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem simple_kills_borel (i : G.rootBase.support) :
    ∀ a ∈ G.borelIdeal, G.simpleRootMap i a = 0 := by
  apply (gaMorphism_kills_hopfIdeal_iff (G.simpleRootMap i) G.borelIdeal).mpr
  apply (tangent_mem_hopfQuotient_iff G.borelIdeal _).mp
  exact ((G.rootWeightSpace_le_borel i.val).mpr
    (G.rootBase.isPos_of_mem_support i.property)) (G.simpleRootMap_tangent_mem i)

/-- The fixed positive simple root morphism factors through the chosen Borel. -/
def simpleBorelRootMap (i : G.rootBase.support) :
    G.borelAlgebra →ₐc[K] SymmetricAlgebra K K :=
  Bialgebra.Quotient.liftBialgHom G.borelIdeal.toIdeal (G.simpleRootMap i)
    (simple_kills_borel G i)

/-- The Borel root factor has the original ambient coordinate morphism. -/
theorem simpleBorelRootMap_comp (i : G.rootBase.support) :
    (simpleBorelRootMap G i).comp
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom =
      G.simpleRootMap i := by
  apply DFunLike.ext
  intro a
  exact Bialgebra.Quotient.liftBialgHom_mk G.borelIdeal.toIdeal
    (G.simpleRootMap i) (simple_kills_borel G i) a

/-- Every regular Borel character is trivial on the fixed simple additive subgroup. -/
theorem borelCharacter_upper_generator (i : G.rootBase.support) (chi : G.characters) :
    ((simpleBorelRootMap G i).comp (borelCharacterMap G chi))
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) = 1 :=
  additiveCharacter_generator ((simpleBorelRootMap G i).comp (borelCharacterMap G chi))

/-- The full coroot character evaluates the odd positive-root character as a single monomial. -/
theorem torusCharacter_coroot_generator (p : ℕ) (hp : Odd p) (i : G.rootBase.support) :
    (MonoidAlgebra.mapDomainBialgHom K (Coroot.simpleCorootCharacter G i))
      (torusCharacterCoordinates G (torusCharacterMap G (G.oddRootCharacter p)
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))) =
      MonoidAlgebra.single (Multiplicative.ofAdd ((p - 1 : ℕ) : ℤ)) 1 := by
  have ht := torusCharacterMap_points G (G.oddRootCharacter p)
    (AlgHom.id K (MonoidAlgebra K G.characters))
  change torusCharacterCoordinates G (torusCharacterMap G (G.oddRootCharacter p)
    (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) =
      MonoidAlgebra.single (G.oddRootCharacter p) 1 at ht
  rw [ht, MonoidAlgebra.mapDomainBialgHom_single]
  have hw : Coroot.simpleCorootCharacter G i (G.oddRootCharacter p) =
      Multiplicative.ofAdd ((p - 1 : ℕ) : ℤ) := by
    change Multiplicative.ofAdd
      (Coroot.simpleCorootFunctional G i (G.oddRootCharacter p).toAdd) = _
    rw [G.oddRootCharacter_weight p hp]
  rw [hw]

end SchubertGeometry.ProjectiveLine
