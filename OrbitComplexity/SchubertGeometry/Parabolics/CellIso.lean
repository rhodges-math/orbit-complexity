import OrbitComplexity.SchubertGeometry.Parabolics.CellActions
import OrbitComplexity.SchubertGeometry.Parabolics.CellProjection
import OrbitComplexity.GroupActions.Varieties.Noetherian
import OrbitComplexity.FrobeniusSplitting.Normality.UniversallyInjective
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Schubert cell isomorphisms under parabolic projection

For a minimum right representative, the smooth cell projection is an isomorphism.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions Topology
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : GroupActions.Variety K}

private theorem iso_of_smooth_points (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    [Surjective f.left] (hf : Function.Injective (Variety.mapPoints f)) : IsIso f.left := by
  let f₀ : X.scheme ⟶ Y.scheme := f.left
  have : Smooth f₀ := inferInstanceAs (Smooth f.left)
  have : Surjective f₀ := inferInstanceAs (Surjective f.left)
  have hw : f₀ ≫ Y.toSpec = X.toSpec := f.w
  have : IsSeparated (f₀ ≫ Y.toSpec) := hw.symm ▸ X.separated
  have : IsSeparated f₀ := IsSeparated.of_comp f₀ Y.toSpec
  have : LocallyOfFiniteType (f₀ ≫ Y.toSpec) := hw.symm ▸ X.locallyOfFiniteType
  have hc : Set.InjOn f₀ (closedPoints X.scheme) := by
    intro x hx y hy hxy
    obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨x, hx⟩
    obtain ⟨q, hq⟩ := X.pointsEquivClosedPoints.surjective ⟨y, hy⟩
    have hpx : X.pointMap p = x := congrArg Subtype.val hp
    have hqy : X.pointMap q = y := congrArg Subtype.val hq
    have he : Variety.mapPoints f p = Variety.mapPoints f q := by
      apply Y.pointMap_injective
      change f₀ (X.pointMap p) = f₀ (X.pointMap q)
      rw [hpx, hqy]
      exact hxy
    exact hpx.symm.trans ((congrArg X.pointMap (hf he)).trans hqy)
  have : UniversallyInjective f₀ :=
    FrobeniusSplitting.universallyInjective_of_closedPoints f₀ Y.toSpec hc
  have : Surjective (pullback.diagonal f₀) :=
    (UniversallyInjective.iff_diagonal f₀).mp inferInstance
  have : IsReduced (pullback f₀ f₀) := inferInstance
  have : IsIso (pullback.diagonal f₀) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.diagonal f₀)
  have : Mono f₀ := (pullback.isIso_diagonal_iff f₀).mp inferInstance
  exact Flat.isIso_of_surjective_of_mono f₀

variable [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)
open ReductiveGroups SchubertGeometry

private theorem cell_injective (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    Function.Injective (Variety.mapPoints (partialCellProjection G J w)) := by
  intro a b hab
  obtain ⟨qa, hqa⟩ := (flagVarietyPointsEquiv G).surjective
    (Variety.mapPoints (schubertCellInclusion G w) a)
  obtain ⟨qb, hqb⟩ := (flagVarietyPointsEquiv G).surjective
    (Variety.mapPoints (schubertCellInclusion G w) b)
  have hfac (y : (schubertCell G w).points) :
      Variety.mapPoints (partialSchubertCellInclusion G J w)
          (Variety.mapPoints (partialCellProjection G J w) y) =
        Variety.mapPoints (partialFlagMorphism G J)
          (Variety.mapPoints (schubertCellInclusion G w) y) := by
    have hc := congrArg (fun f => Variety.mapPoints f y) (partialCellProjection_comp G J w)
    simpa only [Variety.mapPoints_comp] using hc
  have hc := congrArg (Variety.mapPoints (partialSchubertCellInclusion G J w)) hab
  rw [hfac, hfac, ← hqa, ← hqb, partialFlagMorphism_points,
    partialFlagMorphism_points] at hc
  have hq : qa = qb := partialFlagProjection_injOn G J w hw
    (by exact ⟨a, hqa.symm⟩) (by exact ⟨b, hqb.symm⟩)
    ((partialFlagPointsEquiv G J).injective hc)
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
  exact hqa.symm.trans ((congrArg (flagVarietyPointsEquiv G) hq).trans hqb)

/-- A minimum right representative gives an isomorphism on Schubert cells. -/
theorem partialCellProjection_isIso (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    IsIso (partialCellProjection G J w).left := by
  have : Smooth (partialCellProjection G J w).left := partialCellProjection_smooth G J w
  exact iso_of_smooth_points (partialCellProjection G J w) (cell_injective G J w hw)

/-- The Schubert cell isomorphism associated to a minimum right representative. -/
def partialCellIso (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (schubertCell G w).toOver ≅ (partialSchubertCell G J w).toOver := by
  have : IsIso (partialCellProjection G J w).left := partialCellProjection_isIso G J w hw
  exact Over.isoMk (asIso (partialCellProjection G J w).left)
    (partialCellProjection G J w).w

/-- The cell isomorphism is the restriction of the parabolic projection. -/
theorem partialCellIso_hom (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    (partialCellIso G J w hw).hom = partialCellProjection G J w := by
  apply Over.OverMorphism.ext
  rfl

end SchubertGeometry
