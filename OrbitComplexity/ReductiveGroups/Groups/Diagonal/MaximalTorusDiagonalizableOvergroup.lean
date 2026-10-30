import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTorusEnvelope
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Maximal Torus Diagonalizable Overgroup

Maximality of the torus identifies its tangent with that of
every diagonalizable closed overgroup inside the original affine group. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The equality is

```lean
(TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient B.obj Q).hom).range =
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom).range
```
-/
theorem MaximalTorus.diagonalizableOvergroup_tangentImage
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K)
    (I Q : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K B.obj I)
    (hQI : Q ≤ I)
    (hQ : TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B Q)) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient B.obj Q).hom).range =
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom).range := by
  let H := TauCeti.FiniteTypeCommHopfAlgCat.quotient B Q
  let qcat := TauCeti.CommHopfAlgCat.mkQuotient B.obj Q
  let q := qcat.hom
  have hq : Function.Surjective q :=
    TauCeti.CommHopfAlgCat.mkQuotient_surjective B.obj Q
  let IH : TauCeti.HopfIdeal K H := I.map q
  have hIeq : IH.comapOfSurjective q hq = I := by
    exact TauCeti.HopfIdeal.comapOfSurjective_map_mkQuotient hQI
  let ei : TauCeti.FiniteTypeCommHopfAlgCat.quotient B I ≅
      TauCeti.FiniteTypeCommHopfAlgCat.quotient H IH :=
    eqToIso (congrArg (TauCeti.FiniteTypeCommHopfAlgCat.quotient B) hIeq.symm) ≪≫
      ObjectProperty.isoMk _
        (TauCeti.CommHopfAlgCat.quotientIsoOfSurjective qcat hq IH)
  have hItorus : TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H IH) := by
    exact (TauCeti.torusCommHopfAlgProperty K).prop_of_iso ei
      ((TauCeti.HopfIdeal.isMaximalTorus_iff K B.obj I).mp hI).1
  obtain ⟨JH, hJI, hJtorus, hJtop⟩ :=
    diagonalizable_exists_torusEnvelope H hQ IH hItorus
  let JB : TauCeti.HopfIdeal K B := JH.comapOfSurjective q hq
  have hJBI : JB ≤ I := by
    calc
      JB ≤ IH.comapOfSurjective q hq :=
        TauCeti.HopfIdeal.comapOfSurjective_mono q hq hJI
      _ = I := hIeq
  let ej : TauCeti.FiniteTypeCommHopfAlgCat.quotient B JB ≅
      TauCeti.FiniteTypeCommHopfAlgCat.quotient H JH :=
    ObjectProperty.isoMk _
      (TauCeti.CommHopfAlgCat.quotientIsoOfSurjective qcat hq JH)
  have hJBtorus : TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B JB) :=
    (TauCeti.torusCommHopfAlgProperty K).prop_of_iso ej.symm hJtorus
  have hIJB : I ≤ JB :=
    ((TauCeti.HopfIdeal.isMaximalTorus_iff K B.obj I).mp hI).2
      JB hJBtorus hJBI
  have hIJ : JB = I := le_antisymm hJBI hIJB
  -- The envelope's differential is onto the quotient tangent space; descend
  -- an arbitrary tangent to `B/Q` and use ideal membership to conclude.
  apply LieSubalgebra.ext
  intro d
  rw [tangent_mem_hopfQuotient_iff (K := K) (B := B) Q d,
    tangent_mem_hopfQuotient_iff (K := K) (B := B) I d]
  constructor
  · intro hd b hb
    have hdQ : d ∈ (TauCeti.derivationCompLieHom (B := K) q).range :=
      (tangent_mem_hopfQuotient_iff (K := K) (B := B) Q d).mpr hd
    obtain ⟨dH, hde⟩ := hdQ
    have hdHJ : dH ∈ (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient H.obj JH).hom).range := by
      rw [hJtop]
      trivial
    have hkill : ∀ a ∈ JH, dH a = 0 :=
      (tangent_mem_hopfQuotient_iff (K := K) (B := H) JH dH).mp hdHJ
    have hbJ : q b ∈ JH := by
      have hbJB : b ∈ JB := by rw [hIJ]; exact hb
      exact (TauCeti.HopfIdeal.mem_comapOfSurjective).mp hbJB
    have heval := DFunLike.congr_fun hde b
    change TauCeti.derivationComp (B := K) q dH b = d b at heval
    rw [TauCeti.derivationComp_apply] at heval
    exact heval.symm.trans (hkill (q b) hbJ)
  · intro hd b hb
    exact hd b (hQI hb)

end ReductiveGroups
