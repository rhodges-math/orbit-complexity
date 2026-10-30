import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Character
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterLine

/-! # Identification of the determinant scalar with the regular Borel character -/

open ReductiveGroups TauCeti GroupActions WithConv

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- On every Borel point, the determinant scalar equals the full-delta character. -/
theorem positiveDet_borel_character (bq : WithConv (G.borelAlgebra →ₐ[K] K)) :
    ((CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj G.borelIdeal
      (CommAlgCat.of K K)) bq).ofConv (positiveDetCoefficient G) =
        bq.ofConv (borelCharacterMap G G.positiveRootCharacter
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) := by
  let iB := CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj G.borelIdeal
    (CommAlgCat.of K K)
  let b : G.points := iB bq
  have hb : b ∈ G.borelPoints := ⟨bq, rfl⟩
  obtain ⟨z, u, hu, hfactor, hval, _⟩ := positiveDet_borel_factor G b hb
  change ∃ uq, (CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj
    G.unipotentIdeal (CommAlgCat.of K K)) uq = u at hu
  obtain ⟨uq, huq⟩ := hu
  let tq : WithConv (G.borelAlgebra →ₐ[K] K) := toConv
    ((z.ofConv.comp (torusCharacterCoordinates G).toAlgHom).comp
      (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj G.borel_le_torus).hom.toAlgHom)
  let uqB : WithConv (G.borelAlgebra →ₐ[K] K) :=
    TauCeti.AlgHom.mapDomain
      (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
        G.borel_le_unipotentIdeal).hom uq
  have ht : iB tq = TauCeti.AlgHom.mapDomain G.torusSplit z := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    rfl
  have huB : iB uqB = u := by
    calc
      iB uqB = (CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj
          G.unipotentIdeal (CommAlgCat.of K K)) uq := by
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro x
        rfl
      _ = u := huq
  have hbfactor : bq = tq * uqB := by
    apply CommHopfAlgCat.quotientPointsHom_injective G.coordinateAlgebra.obj
      G.borelIdeal (CommAlgCat.of K K)
    change b = iB (tq * uqB)
    calc
      b = TauCeti.AlgHom.mapDomain G.torusSplit z * u := hfactor
      _ = iB tq * iB uqB := congrArg₂ (· * ·) ht.symm huB.symm
      _ = iB (tq * uqB) := (iB.hom.map_mul tq uqB).symm
  have hnative : bq.ofConv (borelCharacterMap G G.positiveRootCharacter
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) =
      z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) := by
    change (↑(ProjectiveLine.borelCharacterUnit G G.positiveRootCharacter bq) : K) = _
    rw [hbfactor, map_mul, Units.val_mul]
    change tq.ofConv (borelCharacterMap G G.positiveRootCharacter
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) *
      uqB.ofConv (borelCharacterMap G G.positiveRootCharacter
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = _
    have huc : uqB.ofConv (borelCharacterMap G G.positiveRootCharacter
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = 1 :=
      borelCharacter_unipotent G G.positiveRootCharacter uq
    rw [huc, mul_one]
    exact borelCharacter_torus G G.positiveRootCharacter z.ofConv
  exact hval.trans hnative.symm

end SchubertGeometry.DeterminantSection
