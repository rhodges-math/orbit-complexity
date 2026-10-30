import OrbitComplexity.ReductiveGroups.Groups.Hopf.HopfIdealNormalBaseChange
import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange

/-!
# Reductive Subgroup Triviality

Descending geometric normal-unipotent triviality to an original Hopf ideal. -/

noncomputable section
namespace ReductiveGroups

open TauCeti CategoryTheory

universe u
variable {K : Type u} [Field K]

/-- A connected normal subgroup of a reductive group whose geometric scalar
extension is smooth unipotent is the identity subgroup over the original field. -/
theorem ReductiveSubgroupTriviality.eq_augmentation_of_geometric_unipotence
    (H : FiniteTypeCommHopfAlgCat.{u, u} K)
    (hH : reductiveCommHopfAlgProperty K H)
    (I : HopfIdeal K H) (hI : I.IsNormal)
    (hconn : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient H I).obj)
    (hU : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K)
        (FiniteTypeCommHopfAlgCat.quotient H I))) :
    I = HopfIdeal.augmentation K H := by
  let J : HopfIdeal (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H) :=
    CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure K) I
  have hJnormal : J.IsNormal := hopfIdeal_isNormal_baseChange H.obj I hI
  let e : FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H) J ≅
      FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K)
        (FiniteTypeCommHopfAlgCat.quotient H I) :=
    ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientBaseChangeIso (K := AlgebraicClosure K) I)
  have hconnbase : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K)
        (FiniteTypeCommHopfAlgCat.quotient H I)).obj :=
    geometricallyConnectedCommHopfAlgProperty.baseChange K (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.quotient H I).obj hconn
  have hconnJ : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H) J).obj :=
    (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure K)).prop_of_iso
      (CommHopfAlgCat.quotientBaseChangeIso (K := AlgebraicClosure K) I).symm
      hconnbase
  have hUJ : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H) J) :=
    (smoothUnipotentCommHopfAlgProperty (AlgebraicClosure K)).prop_of_iso
      e.symm hU
  have hJ : J = HopfIdeal.augmentation (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H) :=
    hH.eq_augmentation J hJnormal hconnJ hUJ
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := AlgebraicClosure K)
  simpa only [CommHopfAlgCat.baseChangeHopfIdeal_augmentation] using hJ

/-- The same descent statement with an unbundled original coordinate ring. -/
theorem ReductiveSubgroupTriviality.of_geometric_unipotence_unbundled
    {B : Type u} [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (I : HopfIdeal K B) (hI : I.IsNormal)
    (hconn : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of K B) I).obj)
    (hU : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure K)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K)
        (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of K B) I))) :
    I = HopfIdeal.augmentation K B :=
  ReductiveSubgroupTriviality.eq_augmentation_of_geometric_unipotence
    (FiniteTypeCommHopfAlgCat.of K B) hB I hI hconn hU

/-- The original-field geometric connectedness and smooth-unipotence
hypotheses suffice to eliminate a normal closed subgroup of a reductive
group. -/
theorem reductive_hopfIdeal_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} K)
    (hH : reductiveCommHopfAlgProperty K H)
    (I : HopfIdeal K H) (hI : I.IsNormal)
    (hconn : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient H I).obj)
    (hU : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient H I)) :
    I = HopfIdeal.augmentation K H :=
  ReductiveSubgroupTriviality.eq_augmentation_of_geometric_unipotence H hH I hI hconn
    (smoothUnipotentCommHopfAlgProperty.baseChange
      (FiniteTypeCommHopfAlgCat.quotient H I) hU)

/-- Original coordinate-ring formulation:  -/
theorem ReductiveSubgroupTriviality.hopfIdeal_eq_augmentation_unbundled
    {B : Type u} [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (I : HopfIdeal K B) (hI : I.IsNormal)
    (hconn : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of K B) I).obj)
    (hU : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of K B) I)) :
    I = HopfIdeal.augmentation K B :=
  reductive_hopfIdeal_eq_augmentation (FiniteTypeCommHopfAlgCat.of K B)
    hB I hI hconn hU

end ReductiveGroups
