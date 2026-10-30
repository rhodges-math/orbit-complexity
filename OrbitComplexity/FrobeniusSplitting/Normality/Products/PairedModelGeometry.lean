import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Batteries.Tactic.Lint

/-! # Geometry of the paired model

The endpoint maps land in the same separated flag model. Their raw pullback is
closed in the product of the two proper word models. Finite presentation and
compactness are derived over the chosen finitely generated coefficient ring.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

noncomputable section

universe u

/-- The raw pair of two proper finitely presented word models is proper,
finitely presented and qcqs. Closedness is derived from the diagonal of the same
separated endpoint model, without a properness premise on the paired source. -/
theorem paired_model_geometry {K : Type u} [Field K]
    (R : Subalgebra ℤ K) (hR : R.FG)
    (X Y F : Over (Spec (.of R)))
    [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    [IsSeparated F.hom] (f : X ⟶ F) (g : Y ⟶ F) :
    let Z := pullback f.left g.left
    let base := pullback.fst f.left g.left ≫ X.hom
    let c := pullback.congrHom f.w g.w
    let j := pullback.mapDesc f.left g.left F.hom ≫ c.hom
    IsClosedImmersion j ∧
      j ≫ pullback.fst X.hom Y.hom = pullback.fst f.left g.left ∧
      j ≫ pullback.snd X.hom Y.hom = pullback.snd f.left g.left ∧
      IsProper base ∧ LocallyOfFinitePresentation base ∧
      CompactSpace Z ∧ QuasiSeparatedSpace Z ∧ IsLocallyNoetherian Z := by
  let : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hR
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let c := pullback.congrHom f.w g.w
  let j := pullback.mapDesc f.left g.left F.hom ≫ c.hom
  let p := pullback.fst X.hom Y.hom ≫ X.hom
  have hj : IsClosedImmersion j := by dsimp only [j]; infer_instance
  let : IsClosedImmersion j := hj
  have hjfst : j ≫ pullback.fst X.hom Y.hom = pullback.fst f.left g.left := by
    dsimp only [j, c, pullback.congrHom, asIso_hom, pullback.mapDesc, pullback.map]
    simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  have hjsnd : j ≫ pullback.snd X.hom Y.hom = pullback.snd f.left g.left := by
    dsimp only [j, c, pullback.congrHom, asIso_hom, pullback.mapDesc, pullback.map]
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hbase : j ≫ p = pullback.fst f.left g.left ≫ X.hom := by
    dsimp only [p]
    rw [← Category.assoc, hjfst]
  have hp : IsProper p := by dsimp only [p]; infer_instance
  let : IsProper p := hp
  have hpFP : LocallyOfFinitePresentation p := by dsimp only [p]; infer_instance
  let : LocallyOfFinitePresentation p := hpFP
  let : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian (pullback f.left g.left) :=
    LocallyOfFiniteType.isLocallyNoetherian j
  have hjFP : LocallyOfFinitePresentation j := inferInstance
  let : LocallyOfFinitePresentation j := hjFP
  have hbproper : IsProper (pullback.fst f.left g.left ≫ X.hom) := by
    rw [← hbase]
    infer_instance
  let : IsProper (pullback.fst f.left g.left ≫ X.hom) := hbproper
  have hbFP : LocallyOfFinitePresentation (pullback.fst f.left g.left ≫ X.hom) := by
    rw [← hbase]
    infer_instance
  exact ⟨hj, hjfst, hjsnd, hbproper, hbFP,
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f.left g.left ≫ X.hom),
    inferInstance, inferInstance⟩

end
end FrobeniusSplitting
