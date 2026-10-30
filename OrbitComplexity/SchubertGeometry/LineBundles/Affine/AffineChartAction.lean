import OrbitComplexity.SchubertGeometry.LineBundles.Modules.ChartLinearization
import OrbitComplexity.SchubertGeometry.Normality.Models.AffineComposition

/-! # Affine-coordinate pullback maps on the specified projective-line chart module -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory GroupActions
universe u
private abbrev affine (R : Type u) [CommRing R] := Spec (.of (Polynomial R))
private abbrev chartModule (R : Type u) [CommRing R] (d : ℕ) :=
  (SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d).restrict
    (projectiveLinePolynomialChart R ⟨0⟩)
private abbrev structureModule (R : Type u) [CommRing R] : (affine R).Modules :=
  SheafOfModules.unit (affine R).ringCatSheaf

/-- The affine coordinate morphism is scaling followed by translation. -/
def projectiveAffineCoordinate (R : Type u) [CommRing R] (c : Rˣ) (b : R) :
    affine R ⟶ affine R :=
  Spec.map (CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC b).toRingHom)

/-- The coordinate morphism is the restriction of the same projective affine map. -/
theorem projectiveAffineCoordinate_chart (R : Type u) [CommRing R] (c : Rˣ) (b : R) :
    projectiveAffineCoordinate R c b ≫ projectiveLinePolynomialChart R ⟨0⟩ =
      projectiveLinePolynomialChart R ⟨0⟩ ≫
        (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso b).hom := by
  rw [projectiveAffineCoordinate, Category.assoc, projectiveLineTranslation_chart,
    ← Category.assoc, projectiveLineScaling_chart, Category.assoc]

/-- The coordinate morphisms obey the same chronological affine composition law. -/
theorem projectiveAffineCoordinate_comp (R : Type u) [CommRing R]
    (c d : Rˣ) (a b : R) :
    projectiveAffineCoordinate R c a ≫ projectiveAffineCoordinate R d b =
      projectiveAffineCoordinate R (d * c) ((d : R) * a + b) := by
  let j := projectiveLinePolynomialChart R ⟨0⟩
  let ac := (projectiveLineScalingIso c).hom ≫ (projectiveLineTranslationIso a).hom
  let ad := (projectiveLineScalingIso d).hom ≫ (projectiveLineTranslationIso b).hom
  let ae := (projectiveLineScalingIso (d * c)).hom ≫
    (projectiveLineTranslationIso ((d : R) * a + b)).hom
  have hc : projectiveAffineCoordinate R c a ≫ j = j ≫ ac :=
    projectiveAffineCoordinate_chart R c a
  have hd : projectiveAffineCoordinate R d b ≫ j = j ≫ ad :=
    projectiveAffineCoordinate_chart R d b
  have he : projectiveAffineCoordinate R (d * c) ((d : R) * a + b) ≫ j = j ≫ ae :=
    projectiveAffineCoordinate_chart R (d * c) ((d : R) * a + b)
  apply (cancel_mono j).mp
  calc
    _ = projectiveAffineCoordinate R c a ≫ (projectiveAffineCoordinate R d b ≫ j) :=
      Category.assoc _ _ _
    _ = projectiveAffineCoordinate R c a ≫ (j ≫ ad) := by rw [hd]
    _ = (projectiveAffineCoordinate R c a ≫ j) ≫ ad := (Category.assoc _ _ _).symm
    _ = (j ≫ ac) ≫ ad := by rw [hc]
    _ = j ≫ ae := by rw [Category.assoc, projectiveAffine_comp]
    _ = _ := he.symm

/-- Unit one and translation zero give the identity on the polynomial chart. -/
theorem projectiveAffineCoordinate_one (R : Type u) [CommRing R] :
    projectiveAffineCoordinate R 1 0 = 𝟙 _ := by
  let j := projectiveLinePolynomialChart R ⟨0⟩
  apply (cancel_mono j).mp
  calc
    _ = j ≫ ((projectiveLineScalingIso (1 : Rˣ)).hom ≫
        (projectiveLineTranslationIso (0 : R)).hom) :=
      projectiveAffineCoordinate_chart R 1 0
    _ = j := by rw [projectiveAffine_one, Category.comp_id]
    _ = _ := (Category.id_comp j).symm

private def coefficientUnit (R : Type u) [CommRing R] (k : Rˣ) : Γ(affine R, ⊤)ˣ :=
  Units.map ((Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom.comp Polynomial.C) k

private theorem coefficientUnit_pullback (R : Type u) [CommRing R]
    (c : Rˣ) (b : R) (k : Rˣ) :
    Units.map (projectiveAffineCoordinate R c b).appTop.hom (coefficientUnit R k) =
      coefficientUnit R k := by
  apply Units.ext
  let r := Polynomial.C (k : R)
  have hs := congrArg (fun h => h r) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom))
  have ht := congrArg (fun h => h r) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC b).toRingHom))
  change ((projectiveAffineCoordinate R c b).appTop)
    ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv r
  change (Spec.map (CommRingCat.ofHom
      (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom)).appTop
    ((Spec.map (CommRingCat.ofHom
      (Polynomial.algEquivAevalXAddC b).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r)) = _
  have hs' : (Spec.map (CommRingCat.ofHom
      (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv r := by
    change (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        ((Polynomial.algEquivCMulXAddC (c : R) 0) (Polynomial.C (k : R))) =
      (Spec.map (CommRingCat.ofHom
        (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) at hs
    exact hs.symm.trans (congrArg (Scheme.ΓSpecIso (.of (Polynomial R))).inv
      ((Polynomial.algEquivCMulXAddC (c : R) 0).commutes (k : R)))
  have ht' : (Spec.map (CommRingCat.ofHom
      (Polynomial.algEquivAevalXAddC b).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv r := by
    change (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        ((Polynomial.algEquivAevalXAddC b) (Polynomial.C (k : R))) =
      (Spec.map (CommRingCat.ofHom
        (Polynomial.algEquivAevalXAddC b).toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) at ht
    exact ht.symm.trans (congrArg (Scheme.ΓSpecIso (.of (Polynomial R))).inv
      ((Polynomial.algEquivAevalXAddC b).commutes (k : R)))
  rw [ht', hs']

private theorem coefficientUnit_mul (R : Type u) [CommRing R] (k l : Rˣ) :
    coefficientUnit R (k * l) = coefficientUnit R k * coefficientUnit R l :=
  by
    apply Units.ext
    change (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        (Polynomial.C ((k : R) * (l : R))) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C (k : R)) *
        (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C (l : R))
    simp only [map_mul]

/-- The specified affine chart module has a weighted pullback isomorphism. -/
def projectiveAffineChartIso (R : Type u) [CommRing R] (d : ℕ)
    (c : Rˣ) (b : R) (k : Rˣ) :
    (Scheme.Modules.pullback (projectiveAffineCoordinate R c b)).obj (chartModule R d) ≅
      chartModule R d :=
  projectiveChartPullbackIso R d (projectiveAffineCoordinate R c b) (coefficientUnit R k)

/-- The affine pullback isomorphism has its prescribed unit multiplier on the chart. -/
theorem projectiveAffineChartIso_chart (R : Type u) [CommRing R] (d : ℕ)
    (c : Rˣ) (b : R) (k : Rˣ) :
    (projectiveAffineChartIso R d c b k).hom ≫
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.pullback (projectiveAffineCoordinate R c b)).map
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom ≫
          (Scheme.Modules.pullbackObjUnitIso (projectiveAffineCoordinate R c b)).hom ≫
            Scheme.Modules.globalSectionsSmul (structureModule R)
              ((Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C (k : R))) :=
  trivializedPullbackIso_chart _ _ _ _

private theorem pullbackIso_congr {X : Scheme.{u}} (M : X.Modules)
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) {f g : X ⟶ X} (h : f = g)
    (a : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pullbackCongr h).hom.app M ≫
        (trivializedPullbackIso M e g a).hom = (trivializedPullbackIso M e f a).hom := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]

/-- The neutral weighted affine chart change is the canonical identity pullback. -/
theorem projectiveAffineChartIso_one (R : Type u) [CommRing R] (d : ℕ) :
    (projectiveAffineChartIso R d 1 0 1).hom =
      (Scheme.Modules.pullbackCongr (projectiveAffineCoordinate_one R)).hom.app
        (chartModule R d) ≫ (Scheme.Modules.pullbackId _).hom.app (chartModule R d) := by
  have h1 : coefficientUnit R 1 = 1 := by
    apply Units.ext
    change (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C 1) = 1
    rw [map_one, map_one]
  change (trivializedPullbackIso (chartModule R d)
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩) (projectiveAffineCoordinate
      R 1 0)
      (coefficientUnit R 1)).hom = _
  rw [h1, ← pullbackIso_congr _ _ (projectiveAffineCoordinate_one R) 1,
    trivializedPullbackIso_id]

/-- The weighted affine chart pullbacks satisfy the sheaf-module composition equation. -/
theorem projectiveAffineChartIso_comp (R : Type u) [CommRing R] (d : ℕ)
    (c e : Rˣ) (a b : R) (k l : Rˣ) :
    (Scheme.Modules.pullbackComp (projectiveAffineCoordinate R c a)
        (projectiveAffineCoordinate R e b)).inv.app (chartModule R d) ≫
      (Scheme.Modules.pullback (projectiveAffineCoordinate R c a)).map
        (projectiveAffineChartIso R d e b l).hom ≫
          (projectiveAffineChartIso R d c a k).hom =
      (Scheme.Modules.pullbackCongr (projectiveAffineCoordinate_comp R c e a b)).hom.app
        (chartModule R d) ≫
          (projectiveAffineChartIso R d (e * c) ((e : R) * a + b) (k * l)).hom := by
  have h := trivializedPullbackIso_comp (chartModule R d)
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩)
    (projectiveAffineCoordinate R c a) (projectiveAffineCoordinate R e b)
    (coefficientUnit R k) (coefficientUnit R l)
  rw [coefficientUnit_pullback, ← coefficientUnit_mul] at h
  exact h.trans (pullbackIso_congr _ _ (projectiveAffineCoordinate_comp R c e a b)
    (coefficientUnit R (k * l))).symm

end SchubertGeometry.ProjectiveLine
