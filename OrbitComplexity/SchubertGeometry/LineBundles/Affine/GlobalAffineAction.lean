import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineGeneratorMaps
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.DiagonalMap

/-! # The global affine pullback map of the projective-line transition module -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
universe u
private abbrev line (R : Type u) [CommRing R] := projectiveScheme R (ULift.{u} (Fin 2))

private theorem affineAction_exists (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    ∃! f : (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).obj
      (SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) ⟶
        SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d,
      (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map (projectiveOrdinaryEval R d) ≫
        f =
          projectiveAffineGeneratorMap R d c b ∧
        f ≫ projectiveTransitionEmbed R d = projectiveAffineChartTarget R d c b := by
  let : Epi (projectiveOrdinaryEval R d) := projectiveOrdinaryEval_epi R d
  let : Epi ((Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map (projectiveOrdinaryEval
    R d)) :=
    inferInstance
  let : Mono (projectiveTransitionEmbed R d) := projectiveTransitionEmbed_mono R d
  exact epiMono_diagonal
    (C := (projectiveScheme R (ULift.{u} (Fin 2))).Modules)
    ((Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map (projectiveOrdinaryEval R d))
    (projectiveTransitionEmbed R d) (projectiveAffineGeneratorMap R d c b)
    (projectiveAffineChartTarget R d c b) (projectiveAffineGenerator_square R d c b)

/-- Affine pullback on the specified global line is determined by its ordinary generators. -/
def projectiveAffineLineMap (R : Type u) [CommRing R] (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).obj
      (SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) ⟶
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d :=
  Classical.choose (affineAction_exists R d c b)

/-- The global pullback map carries both ordinary generators to their transformed sections. -/
theorem projectiveAffineLineMap_generators (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map (projectiveOrdinaryEval R d) ≫
        projectiveAffineLineMap R d c b = projectiveAffineGeneratorMap R d c b :=
  (Classical.choose_spec (affineAction_exists R d c b)).1.1

/-- The global map restricts to the stated invariant polynomial-chart pullback. -/
theorem projectiveAffineLineMap_chart (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    projectiveAffineLineMap R d c b ≫ projectiveTransitionEmbed R d =
      projectiveAffineChartTarget R d c b :=
  (Classical.choose_spec (affineAction_exists R d c b)).1.2

end SchubertGeometry.ProjectiveLine
