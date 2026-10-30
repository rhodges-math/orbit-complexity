import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupAdjointMatrix

/-!
# Conjugated Matrix Representation

Change a faithful matrix embedding by GL conjugation, retaining
the original affine group and its tangents. -/

noncomputable section
namespace ReductiveGroups
open WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
variable (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
  (g : WithConv (TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] K))

/-- The map is surjective:

```lean
Function.Surjective (ρ.comp (affineGroupConjugationBialgHom g))
```
-/
theorem conjugatedMatrixCoordinateMap_surjective (hρ : Function.Surjective ρ) :
    Function.Surjective (ρ.comp (affineGroupConjugationBialgHom g)) :=
  hρ.comp (affineGroupConjugationBialgEquiv g).surjective

/-- The equality is

```lean
TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain (ρ.comp (affineGroupConjugationBialgHom g)) p) =
      TauCeti.GeneralLinear.pointsMulEquiv n g *
        TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ p) *
        (TauCeti.GeneralLinear.pointsMulEquiv n g)⁻¹
```
-/
theorem conjugatedMatrixCoordinateMap_point (p : WithConv (B →ₐ[K] K)) :
    TauCeti.GeneralLinear.pointsMulEquiv n
      (TauCeti.AlgHom.mapDomain (ρ.comp (affineGroupConjugationBialgHom g)) p) =
      TauCeti.GeneralLinear.pointsMulEquiv n g *
        TauCeti.GeneralLinear.pointsMulEquiv n (TauCeti.AlgHom.mapDomain ρ p) *
        (TauCeti.GeneralLinear.pointsMulEquiv n g)⁻¹ := by
  have h := affineGroupConjugationAlgHom_point g (TauCeti.AlgHom.mapDomain ρ p)
  have hs : toConv ((IsScalarTower.toAlgHom K K K).comp g.ofConv) = g := by
    apply WithConv.ofConv_injective
    ext a
    simp
  rw [hs] at h
  have h' := congrArg (TauCeti.GeneralLinear.pointsMulEquiv n) h
  have hc : TauCeti.AlgHom.mapDomain (ρ.comp (affineGroupConjugationBialgHom g)) p =
      toConv (((TauCeti.AlgHom.mapDomain ρ) p).ofConv.comp
        (affineGroupConjugationAlgHom g)) := by
    apply WithConv.ofConv_injective
    ext a
    rfl
  rw [hc]
  simpa only [map_mul, map_inv] using h'

/-- The equality is

```lean
affineGroupMatrixDifferential n (ρ.comp (affineGroupConjugationBialgHom g)) d =
      (TauCeti.GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) K) *
        affineGroupMatrixDifferential n ρ d *
        ((TauCeti.GeneralLinear.pointsMulEquiv n g)⁻¹ :
          Matrix.GeneralLinearGroup (Fin n) K)
```
-/
theorem conjugatedMatrixCoordinateMap_tangent
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    affineGroupMatrixDifferential n (ρ.comp (affineGroupConjugationBialgHom g)) d =
      (TauCeti.GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) K) *
        affineGroupMatrixDifferential n ρ d *
        ((TauCeti.GeneralLinear.pointsMulEquiv n g)⁻¹ :
          Matrix.GeneralLinearGroup (Fin n) K) := by
  rw [affineGroupMatrixDifferential_apply, TauCeti.derivationComp_comp]
  change TauCeti.GeneralLinear.tangentMatrix n
    (TauCeti.derivationComp (B := K) (affineGroupConjugationBialgHom g)
      (TauCeti.derivationComp (B := K) ρ d)) = _
  rw [DerivationComp.conjugation,
    generalLinear_tangentMatrix_adDerivation]
  simp only [generalLinearCounitPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, affineGroupMatrixDifferential_apply]

end ReductiveGroups
