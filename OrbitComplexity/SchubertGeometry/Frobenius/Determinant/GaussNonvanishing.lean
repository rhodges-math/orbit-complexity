import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Word
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Function
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The determinant on the identity Gauss chart

The determinant-power function restricts to one on the opposite unipotent
chart. Consequently its zero support is disjoint from this whole flag chart,
rather than only from the distinguished point.
-/

set_option autoImplicit false
noncomputable section

universe u

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions TauCeti WithConv

namespace SchubertGeometry.DeterminantSection

open private powerCoordinate from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Morphism

private def constantMap {K : Type u} [Field K] (X Y : Variety K)
    (p : Y.points) : X.toOver ⟶ Y.toOver :=
  Over.homMk (X.toSpec ≫ p.val) (by
    change (X.toSpec ≫ p.val) ≫ Y.toSpec = X.toSpec
    rw [Category.assoc, p.property, Category.comp_id])

private theorem constantMap_points {K : Type u} [Field K] (X Y : Variety K)
    (p : Y.points) (x : X.points) : Variety.mapPoints (constantMap X Y p) x = p := by
  apply Subtype.ext
  change x.val ≫ (X.toSpec ≫ p.val) = p.val
  rw [← Category.assoc, x.property, Category.id_comp]

private theorem over_appTop_comp {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : Γ(Z.left, ⊤)) :
    (f ≫ g).left.appTop a = f.left.appTop (g.left.appTop a) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

private theorem appTop_of_eq {S : Scheme.{u}} {X Y : Over S}
    {f g : X ⟶ Y} (h : f = g) (a : Γ(Y.left, ⊤)) :
    f.left.appTop a = g.left.appTop a := by
  cases h
  rfl

private theorem constantMap_appTop {K : Type u} [Field K] (X Y : Variety K)
    (p : Y.points) (a : Γ(Y.scheme, ⊤)) :
    (constantMap X Y p).left.appTop a = X.toSpec.appTop (p.val.appTop a) := by
  change (X.toSpec ≫ p.val).appTop a = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

private theorem spec_section {A B : CommRingCat.{u}} (f : A ⟶ B) (a : A) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv a) =
      (Scheme.ΓSpecIso B).inv (f a) := by
  change ((Scheme.ΓSpecIso A).inv ≫ (Spec.map f).appTop) a = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

private theorem additive_coordinate {K : Type u} [Field K] (t : K) :
    (additivePointsEquiv K t).val.appTop
        ((Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv
          (SymmetricAlgebra.ι K K 1)) =
      (Scheme.ΓSpecIso (.of K)).inv t := by
  let f := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have hp : (additivePointsEquiv K t).val =
      Spec.map (CommRingCat.ofHom f.toRingHom) := rfl
  rw [hp]
  change (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop
    ((Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv
      (SymmetricAlgebra.ι K K 1)) = _
  exact (spec_section (CommRingCat.ofHom f.toRingHom)
    (SymmetricAlgebra.ι K K 1)).trans
      (congrArg ((Scheme.ΓSpecIso (.of K)).inv)
        (AdditiveGroup.gaPointsMulEquiv_symm_apply_ι (Multiplicative.ofAdd t)))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

private theorem power_opposite_one (N : ℕ) (u : G.points)
    (hu : u ∈ G.oppositeUnipotentPoints) : u.ofConv (positiveDetPower G N) = 1 := by
  have h := positiveDetPower_left_unipotent G N u 1 hu
  rw [mul_one] at h
  change u.ofConv (positiveDetPower G N) =
    Coalgebra.counit (R := K) (A := G.coordinateAlgebra) (positiveDetPower G N) at h
  exact h.trans (positiveDetPower_counit G N)

/-- On the identity Gauss chart, the determinant-power morphism is the
constant morphism with value one. -/
theorem positiveDetPower_gauss (N : ℕ) :
    flagChartMap G 1 ≫ positiveDetPowerMorphism G N =
      constantMap (oppositeUnipotentVariety G) (additiveVariety K)
        (additivePointsEquiv K 1) := by
  apply Variety.mapPoints_injective
  funext x
  rw [Variety.mapPoints_comp, flagChartMap_points, positiveDetPowerMorphism_points,
    constantMap_points]
  congr 1
  simpa only [one_mul] using power_opposite_one G N
    (oppositeUnipotentPointsMulEquiv G x) (oppositeUnipotentPointsMulEquiv G x).property

private theorem powerMorphism_coordinate (N : ℕ) :
    (positiveDetPowerMorphism G N).left.appTop
        ((Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv
          (SymmetricAlgebra.ι K K 1)) =
      positiveDetPowerFunction G N := by
  change (Spec.map (CommRingCat.ofHom (powerCoordinate G N).toRingHom)).appTop _ = _
  rw [spec_section]
  change (Scheme.ΓSpecIso (.of G.coordinateAlgebra)).inv
    ((powerCoordinate G N) (SymmetricAlgebra.ι K K 1)) = _
  simp only [powerCoordinate, SymmetricAlgebra.lift_ι_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  rfl

/-- The global determinant-power function is a unit on the entire identity
Gauss chart, with its original chart coordinate equal to one. -/
theorem positiveDetPower_gauss_function (N : ℕ) :
    (flagChartMap G 1).left.appTop (positiveDetPowerFunction G N) = 1 := by
  let c : Γ((additiveVariety K).scheme, ⊤) :=
    (Scheme.ΓSpecIso (.of (SymmetricAlgebra K K))).inv (SymmetricAlgebra.ι K K 1)
  have hc : (positiveDetPowerMorphism G N).left.appTop c =
      positiveDetPowerFunction G N := powerMorphism_coordinate G N
  have hp : (additivePointsEquiv K 1).val.appTop c = 1 := by
    simpa only [map_one] using additive_coordinate (1 : K)
  calc
    (flagChartMap G 1).left.appTop (positiveDetPowerFunction G N) =
        (flagChartMap G 1).left.appTop
          ((positiveDetPowerMorphism G N).left.appTop c) :=
      congrArg ((flagChartMap G 1).left.appTop) hc.symm
    _ = (flagChartMap G 1 ≫ positiveDetPowerMorphism G N).left.appTop c :=
      (over_appTop_comp (X := (oppositeUnipotentVariety G).toOver)
        (Y := (reductiveVariety G).toOver) (Z := (additiveVariety K).toOver)
        (flagChartMap G 1) (positiveDetPowerMorphism G N) c).symm
    _ = (constantMap (oppositeUnipotentVariety G) (additiveVariety K)
        (additivePointsEquiv K 1)).left.appTop c :=
      appTop_of_eq (positiveDetPower_gauss G N) c
    _ = (oppositeUnipotentVariety G).toSpec.appTop
        ((additivePointsEquiv K 1).val.appTop c) :=
      constantMap_appTop (oppositeUnipotentVariety G) (additiveVariety K)
        (additivePointsEquiv K 1) c
    _ = 1 := by rw [hp, map_one]

end SchubertGeometry.DeterminantSection
