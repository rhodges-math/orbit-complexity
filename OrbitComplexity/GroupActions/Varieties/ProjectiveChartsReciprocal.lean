import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme

/-! Reciprocal coordinates on intersections of standard projective charts. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open Opposite HomogeneousLocalization
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroupActions
variable (R ι : Type u) [CommRing R] [Finite ι]

omit [Finite ι] in
private theorem homogeneous_X (j : ι) : X j ∈ homogeneousSubmodule ι R 1 :=
  isHomogeneous_X R j

private theorem chartMap_eq (j : ι) : projectiveChartMap R ι j =
    Spec.map (projectiveChartRingEquiv R ι j).toCommRingCatIso.inv ≫
      Proj.awayι _ _ (homogeneous_X R ι j) Nat.zero_lt_one := by
  simp only [projectiveChartMap, projectiveChartIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, Category.assoc]
  rfl

omit [Finite ι] in
private theorem reciprocal_fraction (i j : ι) :
    awayMap (homogeneousSubmodule ι R) (homogeneous_X R ι j) rfl
        (Away.isLocalizationElem (homogeneous_X R ι i) (homogeneous_X R ι j)) *
      awayMap (homogeneousSubmodule ι R) (homogeneous_X R ι i) (mul_comm (X i) (X j))
        (Away.isLocalizationElem (homogeneous_X R ι j) (homogeneous_X R ι i)) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  simp only [Away.isLocalizationElem, awayMap_mk]
  let s : Submonoid.powers (X i * X j : MvPolynomial ι R) :=
    ⟨(X i * X j) ^ 1, ⟨1, rfl⟩⟩
  change Localization.mk (X j ^ 1 * X j ^ 1) s *
    Localization.mk (X i ^ 1 * X i ^ 1) s = 1
  rw [Localization.mk_mul]
  have hn : (X j ^ 1 * X j ^ 1) * (X i ^ 1 * X i ^ 1) =
      ((s * s : Submonoid.powers (X i * X j : MvPolynomial ι R)) : MvPolynomial ι R) := by
    change _ = (X i * X j) ^ 1 * (X i * X j) ^ 1
    ring
  rw [hn]
  exact Localization.mk_self (s * s)

/-- Coordinates pointing to the other chart multiply to one on a common projective point. -/
theorem projectiveChart_reciprocal (T : Type u) [CommRing T] (i j : ι) (hij : i ≠ j)
    (p : Spec (CommRingCat.of T) ⟶
      Spec (CommRingCat.of (MvPolynomial {k : ι // k ≠ i} R)))
    (q : Spec (CommRingCat.of T) ⟶
      Spec (CommRingCat.of (MvPolynomial {k : ι // k ≠ j} R)))
    (hpq : p ≫ projectiveChartMap R ι i = q ≫ projectiveChartMap R ι j) :
    (Spec.preimage p).hom (X ⟨j, hij.symm⟩) *
      (Spec.preimage q).hom (X ⟨i, hij⟩) = 1 := by
  let a := p ≫ Spec.map (projectiveChartRingEquiv R ι i).toCommRingCatIso.inv
  let b := q ≫ Spec.map (projectiveChartRingEquiv R ι j).toCommRingCatIso.inv
  let fi := Proj.awayι _ _ (homogeneous_X R ι i) Nat.zero_lt_one
  let fj := Proj.awayι _ _ (homogeneous_X R ι j) Nat.zero_lt_one
  have hab : a ≫ fi = b ≫ fj := by
    rw [chartMap_eq, chartMap_eq] at hpq
    exact (Category.assoc _ _ _).trans (hpq.trans (Category.assoc _ _ _).symm)
  let e := Proj.pullbackAwayιIso (homogeneousSubmodule ι R)
    (homogeneous_X R ι i) Nat.zero_lt_one (homogeneous_X R ι j) Nat.zero_lt_one rfl
  let l := pullback.lift a b hab
  let t := l ≫ e.hom
  have ht₁ : t ≫ Spec.map (CommRingCat.ofHom
      (awayMap (homogeneousSubmodule ι R) (homogeneous_X R ι j) rfl)) = a := by
    rw [show t = l ≫ e.hom from rfl, Category.assoc,
      Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left]
    exact pullback.lift_fst _ _ _
  have ht₂ : t ≫ Spec.map (CommRingCat.ofHom
      (awayMap (homogeneousSubmodule ι R) (homogeneous_X R ι i)
        (mul_comm (X i) (X j)))) = b := by
    rw [show t = l ≫ e.hom from rfl, Category.assoc,
      Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right]
    exact pullback.lift_snd _ _ _
  let φ := (Spec.preimage t).hom
  have hp := congrArg Spec.preimage ht₁
  have hq := congrArg Spec.preimage ht₂
  rw [Spec.preimage_comp, Spec.preimage_map] at hp hq
  have hpv := congrArg (fun f => f.hom
    (Away.isLocalizationElem (homogeneous_X R ι i) (homogeneous_X R ι j))) hp
  have hqv := congrArg (fun f => f.hom
    (Away.isLocalizationElem (homogeneous_X R ι j) (homogeneous_X R ι i))) hq
  dsimp only [a, b] at hpv hqv
  rw [Spec.preimage_comp, Spec.preimage_map] at hpv hqv
  change φ _ = (Spec.preimage p).hom ((projectiveChartRingEquiv R ι i).symm _) at hpv
  change φ _ = (Spec.preimage q).hom ((projectiveChartRingEquiv R ι j).symm _) at hqv
  have hpi : (projectiveChartRingEquiv R ι i).symm
      (Away.isLocalizationElem (homogeneous_X R ι i) (homogeneous_X R ι j)) =
        X ⟨j, hij.symm⟩ := by
    rw [← projectiveChartRingEquiv_X R ι i ⟨j, hij.symm⟩, RingEquiv.symm_apply_apply]
  have hqi : (projectiveChartRingEquiv R ι j).symm
      (Away.isLocalizationElem (homogeneous_X R ι j) (homogeneous_X R ι i)) =
        X ⟨i, hij⟩ := by
    rw [← projectiveChartRingEquiv_X R ι j ⟨i, hij⟩, RingEquiv.symm_apply_apply]
  rw [hpi] at hpv
  rw [hqi] at hqv
  rw [← hpv, ← hqv, ← map_mul]
  change φ (awayMap _ (homogeneous_X R ι j) rfl
      (Away.isLocalizationElem (homogeneous_X R ι i) (homogeneous_X R ι j)) *
    awayMap _ (homogeneous_X R ι i) (mul_comm (X i) (X j))
      (Away.isLocalizationElem (homogeneous_X R ι j) (homogeneous_X R ι i))) = 1
  rw [reciprocal_fraction, map_one]

end GroupActions
