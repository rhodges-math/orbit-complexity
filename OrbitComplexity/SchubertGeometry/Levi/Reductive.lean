import OrbitComplexity.SchubertGeometry.Levi.BorelMaximal
import OrbitComplexity.SchubertGeometry.Levi.UnipotentPoints
import OrbitComplexity.SchubertGeometry.Levi.LeviConnected
import OrbitComplexity.SchubertGeometry.Levi.Torus
import OrbitComplexity.ReductiveGroups.Groups.Borel.AlgClosed
import TauCeti.Algebra.AlgebraicGroup.Borel.Radical
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Solvable

/-!
# Reductive standard Levi groups

The Levi Borel is geometrically Borel. Connected normal smooth unipotent
subgroups lie in it by solvable normal containment and are trivial by the
torus-intersection argument. These facts prove geometric reductivity and
assemble the Levi with its inherited split maximal torus and Borel subgroup.
-/

noncomputable section
namespace SchubertGeometry
open TauCeti ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A smooth connected normal unipotent closed subgroup of the standard Levi is trivial. -/
theorem levi_unipotent_eq_augmentation (I : Set G.rootBase.support)
    (J : HopfIdeal K (G.leviAlgebra I)) (hnormal : J.IsNormal)
    (hconnected : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) J).obj)
    (hU : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) J)) :
    J = HopfIdeal.augmentation K (G.leviAlgebra I) := by
  let Q := FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) J
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff K Q).mp hU
  have hUs : geometricallySolvablePointsCommHopfAlgProperty K Q.obj :=
    geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable
      (H := Q) hU'.2
  have hrad : HopfIdeal.IsSolvableRadicalCandidate (G.leviAlgebra I) J :=
    HopfIdeal.IsSolvableRadicalCandidate.mk hnormal hconnected hU'.1 hUs
  have hBJ : leviBorelIdealInLevi G I ≤ J :=
    hrad.le_of_minimal_isBorelCandidate (leviBorel_isBorelOverAlgClosed G I).2
  exact levi_unipotent_eq_of_le G I J hnormal hBJ hU


/-- The selected Levi Borel ideal defines a Borel subgroup after algebraic-closure base change. -/
theorem leviBorel_isBorel (I : Set G.rootBase.support) :
    HopfIdeal.IsBorel K (G.leviAlgebra I).obj (leviBorelIdealInLevi G I) :=
  HopfIdeals.isBorel_of_algClosed (G.leviAlgebra I) (leviBorelIdealInLevi G I)
    (leviBorel_isBorelOverAlgClosed G I)

/-- The standard Levi coordinate algebra represents a connected reductive group. -/
theorem levi_reductive (I : Set G.rootBase.support) :
    reductiveCommHopfAlgProperty K (G.leviAlgebra I) :=
  HopfIdeals.reductive_of_ground (G.leviAlgebra I) (G.levi_smooth I)
    (levi_geometricallyConnected G I) (levi_unipotent_eq_augmentation G I)

/-- The standard Levi with its inherited split maximal torus and Levi Borel subgroup. -/
def leviGroupData (I : Set G.rootBase.support) : ReductiveGroupData K where
  coordinateAlgebra := G.leviAlgebra I
  torusIndex := G.torusIndex
  finiteIndex := G.finiteIndex
  torusIdeal := leviTorusIdeal G I
  borelIdeal := leviBorelIdealInLevi G I
  borel_le_torus := leviBorel_le_torus G I
  isMaximalTorus := leviTorus_isMaximal G I
  isBorel := leviBorel_isBorel G I
  torusSplit := leviTorusSplit G I
  split_surjective := leviTorusSplit_surjective G I
  split_eq_zero := leviTorusSplit_eq_zero G I
  reductive := levi_reductive G I

end SchubertGeometry
