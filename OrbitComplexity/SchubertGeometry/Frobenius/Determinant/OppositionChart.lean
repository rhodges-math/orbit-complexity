import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoefficient
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositeSimpleCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Morphism
import Batteries.Tactic.Lint

/-!
# The regular coefficient on the translated simple chart

The full complementary root variety and the additive line give a translated
opposite-unipotent chart. Its regular determinant coefficient is a constant
unit times an even power of the additive coordinate.
-/

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonoidalCategory
open ReductiveGroups TauCeti GroupActions WithConv
open scoped CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.DeterminantSection

private theorem inverse_coordinates {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {X Y Z H : C} [MonObj H]
    (e : X ⊗ Y ≅ Z) (j : Z ⟶ H) (f : X ⟶ H) (g : Y ⟶ H) (c : H ⟶ H)
    (h : e.hom ≫ j = ((fst X Y ≫ f) * (snd X Y ≫ g)) ≫ c) :
    j = (((e.inv ≫ fst X Y) ≫ f) * ((e.inv ≫ snd X Y) ≫ g)) ≫ c := by
  calc
    _ = (e.inv ≫ e.hom) ≫ j := by rw [e.inv_hom_id, Category.id_comp]
    _ = e.inv ≫ (e.hom ≫ j) := Category.assoc _ _ _
    _ = e.inv ≫ (((fst X Y ≫ f) * (snd X Y ≫ g)) ≫ c) := congrArg (e.inv ≫ ·) h
    _ = (e.inv ≫ ((fst X Y ≫ f) * (snd X Y ≫ g))) ≫ c :=
      (Category.assoc _ _ _).symm
    _ = ((e.inv ≫ (fst X Y ≫ f)) * (e.inv ≫ (snd X Y ≫ g))) ≫ c :=
      congrArg (· ≫ c) (MonObj.comp_mul _ _ _)
    _ = _ := congrArg (· ≫ c)
      (congrArg₂ (· * ·) (Category.assoc e.inv (fst X Y) f).symm
        (Category.assoc e.inv (snd X Y) g).symm)

private theorem iso_precompose {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z) (h : f = e.inv ≫ g) :
    e.hom ≫ f = g := by
  rw [h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem points_mul {K : Type*} [Field K]
    (X H : Variety K) [GrpObj H.toOver] (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

universe u
variable {K : Type u} [Field K]

private def linePowerCoordinate (a : Kˣ) (N : ℕ) :
    SymmetricAlgebra K K →ₐ[K] SymmetricAlgebra K K :=
  SymmetricAlgebra.lift (LinearMap.toSpanSingleton K _
    (algebraMap K (SymmetricAlgebra K K) ((a : K) ^ N) *
      (SymmetricAlgebra.ι K K 1) ^ (2 * N)))

/-- The affine-line map with coordinate polynomial a to the N times X to the 2N. -/
def oppositionPowerMap (a : Kˣ) (N : ℕ) :
    (additiveVariety K).toOver ⟶ (additiveVariety K).toOver :=
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (linePowerCoordinate a N)).op

private theorem powerMap_points (a : Kˣ) (N : ℕ) (t : K) :
    Variety.mapPoints (oppositionPowerMap a N) (additivePointsEquiv K t) =
      additivePointsEquiv K ((a : K) ^ N * t ^ (2 * N)) := by
  let p := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  let q := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd ((a : K) ^ N * t ^ (2 * N)))).ofConv
  have hgen : (p.comp (linePowerCoordinate a N)) (SymmetricAlgebra.ι K K 1) =
      q (SymmetricAlgebra.ι K K 1) := by
    simp [AlgHom.comp_apply, linePowerCoordinate, p, q,
      AdditiveGroup.gaPointsMulEquiv_symm_apply_ι]
  have he : p.comp (linePowerCoordinate a N) = q := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro z
    have hι : SymmetricAlgebra.ι K K z = z • SymmetricAlgebra.ι K K 1 := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (SymmetricAlgebra.ι K K) z (1 : K))
    change (p.comp (linePowerCoordinate a N)) (SymmetricAlgebra.ι K K z) =
      q (SymmetricAlgebra.ι K K z)
    rw [hι, map_smul, map_smul, hgen]
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (linePowerCoordinate a N).toRingHom) =
    Spec.map (CommRingCat.ofHom q.toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun f : SymmetricAlgebra K K →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) he

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private abbrev complement (i : G.rootBase.support) :=
  rootSubsetVariety G
    {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i)}
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i))

private def complementMap (i : G.rootBase.support) :
    (oppositeUnipotentVariety G).toOver ⟶ (complement G i).toOver :=
  (oppositeSimpleCoordinates G i).inv ≫ fst _ _

private def parameterMap (i : G.rootBase.support) :
    (oppositeUnipotentVariety G).toOver ⟶ (additiveVariety K).toOver :=
  (oppositeSimpleCoordinates G i).inv ≫ snd _ _

private def complementPoint (i : G.rootBase.support)
    (x : (oppositeUnipotentVariety G).points) : G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)) :=
  rootSubsetPointsMulEquiv G _ _ (Variety.mapPoints (complementMap G i) x)

private def parameter (i : G.rootBase.support)
    (x : (oppositeUnipotentVariety G).points) : K :=
  (additivePointsEquiv K).symm (Variety.mapPoints (parameterMap G i) x)

private theorem inclusion_points (i : G.rootBase.support)
    (x : (oppositeUnipotentVariety G).points) :
    Variety.mapPoints (oppositeUnipotentInclusion G) x =
      reductivePointsEquiv G
        (G.longestPoint * ((complementPoint G i x : G.points) *
          gaParameterPoint (G.simpleRootMap i) (parameter G i x)) * G.longestPoint⁻¹) := by
  let f : (oppositeUnipotentVariety G).toOver ⟶ (reductiveVariety G).toOver :=
    complementMap G i ≫ rootSubsetInclusion G
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))
  let g : (oppositeUnipotentVariety G).toOver ⟶ (reductiveVariety G).toOver :=
    parameterMap G i ≫ gaMorphism G (G.simpleRootMap i)
  have hc : Variety.mapPoints (X := oppositeUnipotentVariety G) (Y := reductiveVariety G) f x =
      reductivePointsEquiv G (complementPoint G i x) :=
    (Variety.mapPoints_comp (X := oppositeUnipotentVariety G) (Y := complement G i)
      (Z := reductiveVariety G) (complementMap G i) (rootSubsetInclusion G _ _) x).trans
        (rootSubsetInclusion_points G _ _ (Variety.mapPoints (complementMap G i) x))
  have ht : Variety.mapPoints (parameterMap G i) x =
      additivePointsEquiv K (parameter G i x) :=
    ((additivePointsEquiv K).apply_symm_apply _).symm
  have hg : Variety.mapPoints g x =
      reductivePointsEquiv G (gaParameterPoint (G.simpleRootMap i) (parameter G i x)) :=
    (Variety.mapPoints_comp (X := oppositeUnipotentVariety G) (Y := additiveVariety K)
      (Z := reductiveVariety G) (parameterMap G i) (gaMorphism G (G.simpleRootMap i)) x).trans
      ((congrArg (Variety.mapPoints (gaMorphism G (G.simpleRootMap i))) ht).trans
        (gaMorphism_points G (G.simpleRootMap i) (parameter G i x)))
  have hm : Variety.mapPoints (f * g) x = reductivePointsEquiv G
      ((complementPoint G i x : G.points) *
        gaParameterPoint (G.simpleRootMap i) (parameter G i x)) := by
    calc
      _ = Variety.mapPoints f x * Variety.mapPoints g x :=
        points_mul (oppositeUnipotentVariety G) (reductiveVariety G) f g x
      _ = reductivePointsEquiv G (complementPoint G i x) * reductivePointsEquiv G
          (gaParameterPoint (G.simpleRootMap i) (parameter G i x)) := congrArg₂ (· * ·) hc hg
      _ = _ := ((reductivePointsMulEquiv G).map_mul _ _).symm
  have hi : oppositeUnipotentInclusion G = (f * g) ≫
      (reductiveConjugation G G.longestPoint).hom :=
    inverse_coordinates (oppositeSimpleCoordinates G i) (oppositeUnipotentInclusion G)
      (rootSubsetInclusion G _ _) (gaMorphism G (G.simpleRootMap i))
      (reductiveConjugation G G.longestPoint).hom (oppositeSimpleCoordinates_comp G i)
  calc
    _ = Variety.mapPoints ((f * g) ≫ (reductiveConjugation G G.longestPoint).hom) x :=
      congrArg (fun m => Variety.mapPoints m x) hi
    _ = Variety.mapPoints (reductiveConjugation G G.longestPoint).hom
        (Variety.mapPoints (f * g) x) :=
      Variety.mapPoints_comp (X := oppositeUnipotentVariety G) (Y := reductiveVariety G)
        (Z := reductiveVariety G) (f * g) (reductiveConjugation G G.longestPoint).hom x
    _ = _ := (congrArg (Variety.mapPoints (reductiveConjugation G G.longestPoint).hom) hm).trans
      (reductiveConjugation_points G G.longestPoint _)

private theorem chartMap_points (i : G.rootBase.support)
    (x : (oppositeUnipotentVariety G).points) :
    Variety.mapPoints (flagChartMap G (oppositionChartPoint G i)) x =
      reductivePointsEquiv G
        (oppositionRootLift G i (complementPoint G i x) (parameter G i x)) := by
  have hu := (reductivePointsEquiv G).injective
    ((oppositeUnipotentInclusion_points G x).symm.trans (inclusion_points G i x))
  exact (flagChartMap_points G (oppositionChartPoint G i) x).trans
    (congrArg (fun u : G.points => reductivePointsEquiv G (oppositionChartPoint G i * u)) hu)

/-- The translated simple chart is parametrized by the whole complementary root
variety and the specified additive root coordinate. -/
def oppositionChartMap (i : G.rootBase.support) :
    (rootSubsetVariety G
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))).toOver ⊗
      (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  (oppositeSimpleCoordinates G i).hom ≫ flagChartMap G (oppositionChartPoint G i)

/-- The regular coefficient on the full translated chart is its constant unit
times the even power of the additive coordinate, with all complementary variables retained. -/
theorem oppositionChartMap_coefficient (i : G.rootBase.support) :
    ∃ a : Kˣ, ∀ N : ℕ,
      oppositionChartMap G i ≫ positiveDetPowerMorphism G N =
        snd _ _ ≫ oppositionPowerMap a N := by
  obtain ⟨a, ha⟩ := oppositionRootLift_coefficient G i
  refine ⟨a, fun N => ?_⟩
  have hmap : flagChartMap G (oppositionChartPoint G i) ≫ positiveDetPowerMorphism G N =
      parameterMap G i ≫ oppositionPowerMap a N := by
    apply Variety.mapPoints_injective (X := oppositeUnipotentVariety G)
      (Y := additiveVariety K)
    funext x
    calc
      _ = Variety.mapPoints (positiveDetPowerMorphism G N)
          (Variety.mapPoints (flagChartMap G (oppositionChartPoint G i)) x) :=
        Variety.mapPoints_comp _ _ x
      _ = additivePointsEquiv K
          ((oppositionRootLift G i (complementPoint G i x) (parameter G i x)).ofConv
            (positiveDetPower G N)) :=
        (congrArg (Variety.mapPoints (positiveDetPowerMorphism G N))
          (chartMap_points G i x)).trans (positiveDetPowerMorphism_points G N _)
      _ = additivePointsEquiv K ((a : K) ^ N * (parameter G i x) ^ (2 * N)) :=
        congrArg (additivePointsEquiv K)
          (ha N (complementPoint G i x) (complementPoint G i x).property (parameter G i x))
      _ = Variety.mapPoints (oppositionPowerMap a N)
          (additivePointsEquiv K (parameter G i x)) := (powerMap_points a N _).symm
      _ = Variety.mapPoints (oppositionPowerMap a N)
          (Variety.mapPoints (parameterMap G i) x) :=
        congrArg (Variety.mapPoints (oppositionPowerMap a N))
          ((additivePointsEquiv K).apply_symm_apply _)
      _ = _ := (Variety.mapPoints_comp _ _ x).symm
  exact (Category.assoc (oppositeSimpleCoordinates G i).hom
    (flagChartMap G (oppositionChartPoint G i)) (positiveDetPowerMorphism G N)).trans
      (iso_precompose (oppositeSimpleCoordinates G i)
        (flagChartMap G (oppositionChartPoint G i) ≫ positiveDetPowerMorphism G N)
        (snd _ _ ≫ oppositionPowerMap a N) (hmap.trans (Category.assoc _ _ _)))

end SchubertGeometry.DeterminantSection
