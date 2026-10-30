import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframePairs
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenCoframeOverlaps
import OrbitComplexity.FrobeniusSplitting.Cartier.CoframeOverlaps
import Batteries.Tactic.Lint

/-! # Coframes from scalar chart comparisons

Chart coframes on one line module glue when their scalar comparisons are
restrictions of one coframe. Smooth overlap coordinates reflect their
agreement before the module sheaf gluing is applied.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf FrobeniusSplitting.CharacterLine

namespace SchubertGeometry

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A coframe on the fixed line module retaining every specified chart coframe. -/
def scalarCoframeCover {Y : Scheme.{u}} (U : Y.OpenCover.{u}) (L : Y.Modules)
    (E : ∀ i, (Scheme.Modules.pullback (U.f i)).obj L ≅ unitModule (U.X i)) : Prop :=
  ∃ F : L ≅ unitModule Y, ∀ i,
    let : IsOpenImmersion (U.f i) := U.map_prop i
    F.hom.over (U.f i).opensRange = (coframeOverRange (U.f i) L (E i)).hom ∧
      F.inv.over (U.f i).opensRange = (coframeOverRange (U.f i) L (E i)).inv

/-- Scalar comparison with one coframe constructs a coframe on the same line
module, retaining the forward and inverse maps on every chart. -/
theorem scalarCoframe_glue {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {Y Z : Scheme.{u}} [Y.IsSeparated]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (baseK : Z ⟶ Spec (.of K)) (z : Z ⟶ Y)
    (hZ : IsPullback z baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (U : Y.OpenCover.{u}) (hU : ∀ i, IsAffine (U.X i))
    (A : U.I₀ → Scheme.{u}) (j : ∀ i, A i ⟶ Z)
    (v : ∀ i, A i ⟶ U.X i) (hchart : ∀ i, IsPullback (v i) (j i) (U.f i) z)
    (L : Y.Modules) (FK : (Scheme.Modules.pullback z).obj L ≅ unitModule Z)
    (E : ∀ i, (Scheme.Modules.pullback (U.f i)).obj L ≅ unitModule (U.X i))
    (he : ∀ i, squareFrameIso z (j i) (U.f i) (v i) (hchart i).w L (E i) =
      (Scheme.Modules.pullback (j i)).mapIso FK ≪≫ pullbackObjUnitIso (j i)) :
    scalarCoframeCover U L E := by
  apply glueCoframes_of_overlap_eq (fun i => (U.f i).opensRange)
    U.iSup_opensRange L (fun i => coframeOverRange (U.f i) L (E i))
  intro i k
  let : IsAffine (U.X i) := hU i
  let : IsAffine (U.X k) := hU k
  apply ProjectiveCartier.openCoframe_overlap_eq (U.f i) (U.f k) L (E i) (E k)
  exact scalarCoframe_pair_eq hR base (U.f i) (U.f k) (j i) (j k) (v i) (v k) z
    (hchart i).w (hchart k).w (j i ≫ baseK) ((hchart i).paste_vert hZ) (hchart k)
    L FK (E i) (E k) (he i) (he k)

end SchubertGeometry
