import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Borel
import OrbitComplexity.SchubertGeometry.Normality.SchubertBorelCharacter

/-! # character values on the torus and unipotent factors -/

open ReductiveGroups TauCeti GroupActions
open scoped TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
@[instance_reducible]
private def scalarComodule {H : Type u} [CommRing H] [HopfAlgebra K H]
    (h : H) (hh : IsGroupLikeElem K h) : Comodule K H K where
  coact := (TensorProduct.mk K K H).flip h
  coassoc := by
    apply LinearMap.ext
    intro a
    simp [hh.comul_eq_tmul_self]
  lTensor_counit_comp_coact := by
    apply LinearMap.ext
    intro a
    simp [hh.counit_eq_one]

omit [IsAlgClosed K] [CharZero K] in
private theorem unipotent_character {H : Type u} [CommRing H] [HopfAlgebra K H]
    (g : WithConv (H →ₐ[K] K)) (hg : HopfAlgebra.IsUnipotentPoint g)
    (h : H) (hh : IsGroupLikeElem K h) : g.ofConv h = 1 := by
  let := scalarComodule h hh
  let M := FGComoduleCat.of (R := K) (C := H) K
  have hdim : Module.finrank K (K ⊗[K] M) = 1 := by
    exact (TensorProduct.lid K K).finrank_eq.trans (Module.finrank_self K)
  have hone := (hg M).eq_one_of_finrank_eq_one hdim
  have ha : Comodule.endOfPoint M g.ofConv (1 ⊗ₜ[K] (1 : K)) =
      (1 ⊗ₜ[K] (1 : K)) := by
    rw [← Comodule.pointsAction_toLinearMap]
    have he := congrArg (fun f : LinearMap.GeneralLinearGroup K (K ⊗[K] M) =>
      f • ((1 : K) ⊗ₜ[K] (1 : K))) hone
    simpa only [LinearMap.GeneralLinearGroup.ofLinearEquiv_smul,
      one_smul, LinearEquiv.coe_toLinearMap] using he
  rw [Comodule.endOfPoint_tmul] at ha
  change (1 : K) • TensorProduct.comm K K K
    (LinearMap.lTensor K g.ofConv.toLinearMap ((1 : K) ⊗ₜ[K] h)) =
      ((1 : K) ⊗ₜ[K] (1 : K)) at ha
  have hs := congrArg (TensorProduct.lid K K) ha
  simpa only [one_smul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    TensorProduct.comm_tmul, TensorProduct.lid_tmul, smul_eq_mul, mul_one] using hs

/-- A Borel character is trivial on the positive-unipotent subgroup. -/
theorem borelCharacter_unipotent (chi : G.characters)
    (u : WithConv (G.unipotentAlgebra →ₐ[K] K)) :
    (TauCeti.AlgHom.mapDomain
      (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
        G.borel_le_unipotentIdeal).hom u).ofConv
      (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = 1 := by
  let : Algebra.Smooth K G.unipotentAlgebra := G.unipotent_smooth
  let : IsReduced G.unipotentAlgebra := isReduced_of_smooth K G.unipotentAlgebra
  have hu := geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint
    G.unipotent_geometricallyUnipotent u
  let q := (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
    G.borel_le_unipotentIdeal).hom
  have hc : IsGroupLikeElem K (q (borelCharacterMap G chi (MonoidAlgebra.single
    (Multiplicative.ofAdd 1) 1))) := by
    exact ((MonoidAlgebra.isGroupLikeElem_single_one
      (R := K) (Multiplicative.ofAdd (1 : ℤ))).map
        (borelCharacterMap G chi)).map q
  exact unipotent_character u hu _ hc

/-- Restricting the Borel character to the chosen split torus reads the full character. -/
theorem borelCharacter_torus (chi : G.characters)
    (z : MonoidAlgebra K G.characters →ₐ[K] K) :
    (((z.comp (torusCharacterCoordinates G).toAlgHom).comp
      (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj G.borel_le_torus).hom.toAlgHom)
        (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))) = z
          (MonoidAlgebra.single chi 1) := by
  have he := congrArg (fun f : MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] G.torusAlgebra =>
    (z.comp (torusCharacterCoordinates G).toAlgHom)
      (f (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))
      (borelCharacterMap_restrict G chi)
  exact he.trans (torusCharacterMap_points G chi z)

end SchubertGeometry.DeterminantSection
