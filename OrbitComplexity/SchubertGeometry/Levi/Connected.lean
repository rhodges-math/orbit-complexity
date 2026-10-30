import OrbitComplexity.SchubertGeometry.Levi.Dimension
import TauCeti.Algebra.AlgebraicGroup.Borel.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Connected Levi Borel subgroups

The torus and positive Levi-root product maps onto the Levi Borel subgroup.
Its integral image gives geometric connectedness. The quotient from the
ambient Borel supplies geometric solvability inside the Levi group.
-/

open CategoryTheory AlgebraicGeometry GroupActions TauCeti ReductiveGroups

noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The Levi--Borel variety is integral, as the surjective image of its torus--root product. -/
instance leviBorel_integral (I : Set G.rootBase.support) :
    IsIntegral (leviBorelVariety G I).scheme := by
  have : IsIntegral (leviBorelProduct G I).scheme := Variety.product_integral _ _
  have : IrreducibleSpace (leviBorelVariety G I).scheme :=
    Variety.irreducible_of_surjective_points (leviBorelMultiplication G I)
      (leviBorelMultiplication_bijective G I).2
  exact isIntegral_of_irreducibleSpace_of_isReduced (leviBorelVariety G I).scheme

private def leviBorelMap (I : Set G.rootBase.support) :
    (G.leviAlgebra I).obj ⟶ (G.leviBorelAlgebra I).obj :=
  CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra)
    (G.leviIdeal_le_leviBorel I)

private theorem leviBorelMap_surjective (I : Set G.rootBase.support) :
    Function.Surjective (leviBorelMap G I).hom :=
  CommHopfAlgCat.quotientMapOfLe_surjective (CommHopfAlgCat.of K G.coordinateAlgebra)
    (G.leviIdeal_le_leviBorel I)

/-- The defining Hopf ideal of the Levi--Borel subgroup inside the Levi coordinate algebra. -/
def leviBorelIdealInLevi (I : Set G.rootBase.support) : HopfIdeal K (G.leviAlgebra I) :=
  HopfIdeal.kerOfSurjective (leviBorelMap G I).hom (leviBorelMap_surjective G I)

/-- The quotient by the Levi--Borel ideal inside the Levi is its original coordinate algebra. -/
def leviBorelQuotientIso (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotient (G.leviAlgebra I).obj (leviBorelIdealInLevi G I) ≅
      (G.leviBorelAlgebra I).obj :=
  CommHopfAlgCat.quotientKerOfSurjectiveIso (leviBorelMap G I) (leviBorelMap_surjective G I)

private theorem leviBorel_connected (I : Set G.rootBase.support) :
    geometricallyConnectedCommHopfAlgProperty K (G.leviBorelAlgebra I).obj := by
  apply (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace K _).mpr
  change ConnectedSpace (leviBorelVariety G I).scheme
  infer_instance

private theorem leviBorel_solvable (I : Set G.rootBase.support) :
    geometricallySolvablePointsCommHopfAlgProperty K (G.leviBorelAlgebra I).obj := by
  let f : G.borelAlgebra.obj ⟶ (G.leviBorelAlgebra I).obj :=
    CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.borelIdeal_le_leviBorel I)
  have hf : Function.Surjective f.hom :=
    CommHopfAlgCat.quotientMapOfLe_surjective (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.borelIdeal_le_leviBorel I)
  have hb : geometricallySolvablePointsCommHopfAlgProperty K G.borelAlgebra.obj :=
    G.isBorel.isBorelCandidate.geometricallySolvable
  exact geometricallySolvablePointsCommHopfAlgProperty_of_surjective K f hf hb

/-- The Levi--Borel subgroup inside the Levi is smooth, geometrically connected,
and geometrically solvable. -/
theorem leviBorel_candidate (I : Set G.rootBase.support) :
    HopfIdeal.IsBorelCandidate K (G.leviAlgebra I) (leviBorelIdealInLevi G I) := by
  let e := leviBorelQuotientIso G I
  apply HopfIdeal.IsBorelCandidate.mk
  · apply (smoothCommHopfAlgProperty K).prop_of_iso e.symm
    exact (smoothCommHopfAlgProperty_iff _).mpr (G.leviBorel_smooth I)
  · exact (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso e.symm
      (leviBorel_connected G I)
  · exact (geometricallySolvablePointsCommHopfAlgProperty K).prop_of_iso e.symm
      (leviBorel_solvable G I)

end SchubertGeometry
