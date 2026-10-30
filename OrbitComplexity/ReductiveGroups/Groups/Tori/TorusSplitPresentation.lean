import OrbitComplexity.ReductiveGroups.Groups.Hopf.HopfBaseChangeDescent
import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# Torus Split Presentation

A torus over an algebraically closed field is split over the
original field, by descent of its defining scalar-extended Hopf isomorphism. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The geometric torus property gives a split presentation over the original
algebraically closed field, without changing the torus coordinate algebra. -/
theorem torus_split_of_isAlgClosed
    (Q : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K)
    (hQ : TauCeti.torusCommHopfAlgProperty K Q) :
    TauCeti.splitTorusCommHopfAlgProperty K Q := by
  obtain ⟨n, ⟨e⟩⟩ := (TauCeti.torusCommHopfAlgProperty_iff K Q).mp hQ
  let A := TauCeti.DiagonalizableGroup.coordinateRing K
    (TauCeti.SplitTorus.characterGroup (ULift.{u} (Fin n)))
  let ei : TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) A ≅
      TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) Q :=
    TauCeti.DiagonalizableGroup.baseChangeCoordinateRingIso K (AlgebraicClosure K)
      (TauCeti.SplitTorus.characterGroup (ULift.{u} (Fin n))) ≪≫ e
  let eb := (forget₂ (TauCeti.FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure K))
    (CommHopfAlgCat.{u} (AlgebraicClosure K))).mapIso ei
  let e0 : A.obj ≅ Q.obj := hopfIsoOfBaseChangeIso
    (IsAlgClosure.equiv K K (AlgebraicClosure K)) A.obj Q.obj eb
  exact ⟨n, ⟨ObjectProperty.isoMk _ e0⟩⟩

end ReductiveGroups
