import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Noetherian
import OrbitComplexity.SchubertGeometry.Connectedness.RootEndpointMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.CommonCurveModels

/-!
# Common models of Richardson root curves and their endpoints

The Richardson-valued reflection-root curves retain both endpoint triangles
above a common coefficient stage. Their targets and anchor maps are extensions
of the specified arithmetic target and the specified initial anchors.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting GroupActions ReductiveGroups

noncomputable section

namespace SchubertGeometry.CellContraction

universe u v

private theorem bool_triangles {T : Type*} [Category T] {A P D : T}
    (s : Bool → (A ⟶ P)) (c : P ⟶ D) (a₀ a₁ : A ⟶ D)
    (h₀ : s false ≫ c = a₀) (h₁ : s true ≫ c = a₁) :
    ∀ e : Bool, s e ≫ c = if e then a₁ else a₀
  | false => h₀
  | true => h₁

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- A finite family of Richardson root curves retains both endpoints with a
single curve map per edge, incident to extensions of the chosen initial anchors. -/
theorem exists_root_endpoint_models
    (a b : G.weylGroup) (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Fintype I] (w : I → G.weylGroup)
    (i : I → G.rootBase.support) (x : I → G.weylGroup)
    (hroot : ∀ z : I, G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm (w z) (i z).val))
    (hpos : ∀ z : I, G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm (x z)⁻¹
        (G.rootSystem.weylGroupToPerm (w z) (i z).val)))
    (hax : ∀ z : I, WeylBruhatLE G.rootBase a (x z))
    (hxy : ∀ z : I, WeylBruhatLE G.rootBase (x z)
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z))
    (hyb : ∀ z : I, WeylBruhatLE G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z) b)
    (hne₀ : ∀ z : I, Nonempty (cellIntersection G a b (x z)).left)
    (hne₁ : ∀ z : I, Nonempty (cellIntersection G a b
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z)).left)
    (D : Over (Spec (.of S))) [LocallyOfFinitePresentation D.hom]
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S)
    (anchor : ∀ _r : I × Bool, stageScalarModel S (𝟙 (Spec (.of S))) start ⟶
      stageScalarModel S D.hom start)
    (ha : ∀ r : I × Bool,
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op start) ≫ (anchor r).left =
        (if r.2 then
          cellAnchorGenericMap G a b
            (RootPairing.weylGroup.ofIdx G.rootSystem
              (G.rootSystem.weylGroupToPerm (w r.1) (i r.1).val) * x r.1)
            (hne₁ r.1) S D qD hD
        else cellAnchorGenericMap G a b (x r.1) (hne₀ r.1) S D qD hD).left ≫
          (modelScalarCone S D.hom).π.app (op start)) :
    ∃ (l : CoefficientStage S) (hsl : start ≤ l)
      (j : CoefficientStage S) (hlj : l ≤ j)
      (k : CoefficientStage S) (hjk : j ≤ k)
      (s : ∀ _r : I × Bool, stageScalarModel S (𝟙 (Spec (.of S))) k ⟶
        stageScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) k)
      (c : ∀ _z : I, stageScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) k ⟶
        stageScalarModel S D.hom k), ∀ r : I × Bool,
      s r ≫ c r.1 = extendModelMorphism S (𝟙 (Spec (.of S))) D.hom hjk
        (extendModelMorphism S (𝟙 (Spec (.of S))) D.hom hlj
          (extendModelMorphism S (𝟙 (Spec (.of S))) D.hom hsl (anchor r))) ∧
      (modelScalarCone S (𝟙 (Spec (.of S)))).π.app (op k) ≫ (s r).left =
        (rootEndpointGenericMap S r.2).left ≫
          (modelScalarCone S (projectiveToSpec S (ULift.{u} (Fin 2)))).π.app (op k) ∧
      (modelScalarCone S (projectiveToSpec S (ULift.{u} (Fin 2)))).π.app (op k) ≫
          (c r.1).left =
        (projectiveGenericMap S (ULift.{u} (Fin 2)) D (richardsonVariety G a b).toOver
          qD hD (rootCurveRichardson G (w r.1) (i r.1) a (x r.1) b
            (hroot r.1) (hpos r.1) (hax r.1) (hxy r.1) (hyb r.1))).left ≫
          (modelScalarCone S D.hom).π.app (op k) := by
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let : CompactSpace (projectiveScheme S (ULift.{u} (Fin 2))) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveToSpec S (ULift.{u} (Fin 2)))
  let : QuasiSeparatedSpace (projectiveScheme S (ULift.{u} (Fin 2))) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveToSpec S (ULift.{u} (Fin 2)))
  let sK : ∀ _r : I × Bool, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) :=
    fun r => rootEndpointGenericMap S r.2
  let cK : ∀ _z : I, genericScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) ⟶
      genericScalarModel S D.hom := fun z =>
    projectiveGenericMap S (ULift.{u} (Fin 2)) D (richardsonVariety G a b).toOver qD hD
      (rootCurveRichardson G (w z) (i z) a (x z) b
        (hroot z) (hpos z) (hax z) (hxy z) (hyb z))
  let aK : ∀ _r : I × Bool, genericScalarModel S (𝟙 (Spec (.of S))) ⟶
      genericScalarModel S D.hom := fun r =>
    if r.2 then cellAnchorGenericMap G a b
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w r.1) (i r.1).val) * x r.1)
      (hne₁ r.1) S D qD hD
    else cellAnchorGenericMap G a b (x r.1) (hne₀ r.1) S D qD hD
  have he : ∀ r : I × Bool, sK r ≫ cK r.1 = aK r := fun r =>
    bool_triangles (rootEndpointGenericMap S) (cK r.1) _ _
      (rootCurve_zero_triangle G (w r.1) (i r.1) a (x r.1) b
        (hroot r.1) (hpos r.1) (hax r.1) (hxy r.1) (hyb r.1) (hne₀ r.1) S D qD hD)
      (rootCurve_infinity_triangle G (w r.1) (i r.1) a (x r.1) b
        (hroot r.1) (hpos r.1) (hax r.1) (hxy r.1) (hyb r.1) (hne₁ r.1) S D qD hD) r.2
  exact exists_common_curve_models S hS
    (fun _ : I => projectiveScheme S (ULift.{u} (Fin 2)))
    (fun _ => projectiveToSpec S (ULift.{u} (Fin 2))) D.hom sK cK aK he start anchor ha

end SchubertGeometry.CellContraction
