import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.DeterminantSection
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Unit
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedSectionComparison
import OrbitComplexity.FrobeniusSplitting.Splittings.Field
import OrbitComplexity.FrobeniusSplitting.Splittings.Spec
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.CharP.Algebra
import Batteries.Tactic.Lint

/-! # The empty-word section and normalized field prior

The original empty-word determinant section is the unit in its group-unit
coframe. Its unit-line model therefore specializes to the unit section over
any residue field. A field splitting constructs the twisted prior there;
perfectness is required only of a separately chosen constant field.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine
open scoped CategoryTheory.MonObj TensorProduct
namespace SchubertGeometry.ProjectiveCartier
universe u

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem pullSection_transpose {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : unitModule Y ⟶ M)
    (c : M ⟶ (pushforward f).obj (unitModule X)) (r : Γ(X, ⊤))
    (hs : s ≫ c = relativeCoefficient Y (Over.mk f) r) :
    ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) ≫
        ((pullbackPushforwardAdjunction f).homEquiv M (unitModule X)).symm c =
      globalSectionsSmul (unitModule X) r := by
  have hn := (pullbackPushforwardAdjunction f).homEquiv_naturality_left_symm s c
  have hc : ((pullbackPushforwardAdjunction f).homEquiv (unitModule Y) (unitModule X)).symm
      (relativeCoefficient Y (Over.mk f) r) =
      (pullbackObjUnitIso f).hom ≫ globalSectionsSmul (unitModule X) r := by
    have hu : ((pullbackPushforwardAdjunction f).homEquiv (unitModule Y) (unitModule X)).symm
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
        (pullbackObjUnitIso f).hom := by
      apply ((pullbackPushforwardAdjunction f).homEquiv (unitModule Y) (unitModule X)).injective
      exact (((pullbackPushforwardAdjunction f).homEquiv (unitModule Y)
        (unitModule X)).apply_symm_apply _).trans
          (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f).symm
    change ((pullbackPushforwardAdjunction f).homEquiv (unitModule Y) (unitModule X)).symm
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (pushforward f).map (globalSectionsSmul (unitModule X) r)) = _
    exact ((pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      (globalSectionsSmul (unitModule X) r)).trans
        (congrArg (fun t => t ≫ globalSectionsSmul (unitModule X) r) hu)
  calc
    ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) ≫
        ((pullbackPushforwardAdjunction f).homEquiv M (unitModule X)).symm c =
      (pullbackObjUnitIso f).inv ≫
        ((Scheme.Modules.pullback f).map s ≫
          ((pullbackPushforwardAdjunction f).homEquiv M (unitModule X)).symm c) :=
        Category.assoc _ _ _
    _ = (pullbackObjUnitIso f).inv ≫
        ((pullbackPushforwardAdjunction f).homEquiv (unitModule Y) (unitModule X)).symm
          (s ≫ c) := congrArg (fun t => (pullbackObjUnitIso f).inv ≫ t) hn.symm
    _ = (pullbackObjUnitIso f).inv ≫
        ((pullbackObjUnitIso f).hom ≫ globalSectionsSmul (unitModule X) r) :=
      congrArg (fun t => (pullbackObjUnitIso f).inv ≫ t)
        ((congrArg (((pullbackPushforwardAdjunction f).homEquiv
          (unitModule Y) (unitModule X)).symm) hs).trans hc)
    _ = globalSectionsSmul (unitModule X) r := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private def frameSectionOne {X : Scheme.{u}} (M : X.Modules)
    (s : unitModule X ⟶ M) (E : M ≅ unitModule X) : Prop :=
  s ≫ E.hom = 𝟙 (unitModule X)

private theorem frameSection_transpose {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : unitModule Y ⟶ M)
    (E : (Scheme.Modules.pullback f).obj M ≅ unitModule X)
    (c : M ⟶ (pushforward f).obj (unitModule X))
    (hE : E.hom = ((pullbackPushforwardAdjunction f).homEquiv M (unitModule X)).symm c)
    (hs : s ≫ c = relativeCoefficient Y (Over.mk f) (1 : Γ(X, ⊤))) :
    frameSectionOne ((Scheme.Modules.pullback f).obj M)
      ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) E := by
  change ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) ≫ E.hom = _
  rw [hE]
  exact (pullSection_transpose f M s c (1 : Γ(X, ⊤)) hs).trans
    (RelativeGlue.globalSmul_one (unitModule X))

private theorem quotient_unit_of_point {K P : Type u} [Field K] [MulOneClass P]
    (H : Variety K) [GrpObj H.toOver] (E : P ≃* H.points)
    {Y : Scheme.{u}} (q : H.scheme ⟶ Y) (z : Spec (.of K) ⟶ Y)
    (hq : (E 1).val ≫ q = z) :
    η[H.toOver].left ≫ q = z := by
  have hu : (1 : H.points).val = η[H.toOver].left :=
    congrArg Over.Hom.left (Variety.pointsEquivOverHom_one H)
  have hp : (E 1).val = η[H.toOver].left :=
    (congrArg (fun x : H.points => x.val) E.map_one).trans hu
  exact (congrArg (fun f : Spec (.of K) ⟶ H.scheme => f ≫ q) hp.symm).trans hq

private def evaluationComposite {S : Scheme.{u}} {M N P : S.Modules}
    (i : M ⟶ N) (r : N ⟶ P) : M ⟶ P := i ≫ r

private theorem frameSection_factor {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (r : X ⟶ Y) (hr : r ≫ g = f)
    (M : S.Modules) (s : unitModule S ⟶ M)
    (i : M ⟶ (pushforward g).obj (unitModule Y)) (F : Γ(Y, ⊤))
    (hs : s ≫ i = relativeCoefficient S (Over.mk g) F)
    (hv : r.appTop F = (1 : Γ(X, ⊤)))
    (E : (Scheme.Modules.pullback f).obj M ≅ unitModule X)
    (hE : E.hom = ((pullbackPushforwardAdjunction f).homEquiv M (unitModule X)).symm
      (evaluationComposite i (relativeFunctionsMap S
        (X := Over.mk f) (Y := Over.mk g) (Over.homMk r hr)))) :
    frameSectionOne ((Scheme.Modules.pullback f).obj M)
      ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) E := by
  let a : Over.mk f ⟶ Over.mk g := Over.homMk r hr
  let v : (pushforward g).obj (unitModule Y) ⟶
      (pushforward f).obj (unitModule X) :=
    relativeFunctionsMap S (X := Over.mk f) (Y := Over.mk g) a
  let c : M ⟶ (pushforward f).obj (unitModule X) := i ≫ v
  have hfun := relativeCoefficient_pullback S a F
  have hsi : (s ≫ i) ≫ v = relativeCoefficient S (Over.mk g) F ≫ v :=
    congrArg (fun t : unitModule S ⟶ (pushforward g).obj (unitModule Y) => t ≫ v) hs
  have hlast : relativeCoefficient S (Over.mk f) (r.appTop F) =
      relativeCoefficient S (Over.mk f) (1 : Γ(X, ⊤)) :=
    congrArg (relativeCoefficient S (Over.mk f)) hv
  have hc : s ≫ c = relativeCoefficient S (Over.mk f) (1 : Γ(X, ⊤)) :=
    (Category.assoc s i v).symm.trans (hsi.trans (hfun.trans hlast))

  exact frameSection_transpose f M s E c hE hc

section Word
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

private theorem empty_unit_endpoint :
    η[(reductiveVariety G).toOver].left ≫ flagQuotient G = bsdhMap G [] := by
  have hq := flagQuotient_points G (1 : G.points)
  have hp := quotient_unit_of_point (reductiveVariety G) (reductivePointsMulEquiv G)
    (flagQuotient G) _ hq
  exact hp

/-- The original empty-word character line has the coframe obtained by
evaluating the full character at the identity section of the group. -/
def emptyWordFrame (N : ℕ) :
    CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ N) [] ≅
      unitModule (Spec (.of K)) := by
  let M : (Spec (.of K)).Modules :=
    CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ N) []
  let E : M ⟶ unitModule (Spec (.of K)) := CharacterLine.characterFrameEvaluation G
      (G.positiveRootCharacter ^ N)
    (Over.mk (𝟙 (Spec (.of K)))) (bsdhMap G [])
    η[(reductiveVariety G).toOver] (empty_unit_endpoint G)
  let hE : IsIso E := CharacterLine.characterFrameEvaluation_isIso G
    (G.positiveRootCharacter ^ N) (Over.mk (𝟙 (Spec (.of K))))
    (bsdhMap G []) η[(reductiveVariety G).toOver] (empty_unit_endpoint G)
  exact @asIso (Spec (.of K)).Modules _ M (unitModule (Spec (.of K))) E hE

/-- The original determinant section on the empty word is the unit section
in the constructed identity coframe, for every character power. -/
theorem emptyWordSection_frame (N : ℕ) :
    frameSectionOne (X := Spec (.of K))
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ N) [])
      (CharacterLine.wordDeterminantModuleSection G N []) (emptyWordFrame G N) := by
  have hi := CharacterLine.flagDeterminantModuleSection_inclusion G N
  have hv := DeterminantSection.positiveDetPower_unit G N
  exact frameSection_factor (S := (flagVariety G).scheme)
    (X := Spec (.of K)) (Y := (reductiveVariety G).scheme)
    (bsdhMap G []) (flagQuotient G) η[(reductiveVariety G).toOver].left
    (empty_unit_endpoint G)
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N))
    (CharacterLine.flagDeterminantModuleSection G N)
    (CharacterLine.flagCharacterInclusion G (G.positiveRootCharacter ^ N))
    (DeterminantSection.positiveDetPowerFunction G N) hi hv (emptyWordFrame G N) rfl

end Word

section Field
variable {C L : Type u} [CommRing C] [Field L]
    {p : ℕ} [ExpChar C p] [ExpChar L p]
    (base : Spec (.of L) ⟶ Spec (.of C))

private abbrev fieldSplitting :=
  (RingSplitting.ofField L p).toSpec (expChar_pos L p)

/-- The empty-word twisted prior over an arbitrary field is constructed
from a splitting of that field, with a separately specified constant base. -/
def fieldTwistedPrior :
    frobeniusRestriction C p base (unitModule (Spec (.of L))) ⟶ unitModule (Spec (.of L)) :=
  RelativeGlue.schemeOperatorHom base (fieldSplitting (L := L) (p := p)).toOperator

/-- The constructed field prior takes the empty-word unit section to one. -/
theorem fieldTwistedPrior_one :
    (fieldTwistedPrior (p := p) base).app ⊤ (1 : Γ(Spec (.of L), ⊤)) =
      (1 : Γ(Spec (.of L), ⊤)) :=
  ((fieldSplitting (L := L) (p := p)).onOpen ⊤).map_one

/-- Inserting the empty-word unit section gives the original field operator
with no additional scalar weight. -/
theorem fieldTwistedPrior_operator :
    twistedSectionOperator base (unitModule (Spec (.of L))) (fieldTwistedPrior (p := p) base)
      (1 : Γ(Spec (.of L), ⊤)) =
      (fieldSplitting (L := L) (p := p)).toOperator := by
  apply SchemeFrobeniusMap.ext
  intro U a
  change (fieldSplitting (L := L) (p := p)).onOpen U
    (a * (Spec (.of L)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1) =
    (fieldSplitting (L := L) (p := p)).onOpen U a
  rw [map_one, mul_one]

/-- The same retained determinant coefficient is normalized after every
field specialization, since its counit comparison already forces it to one. -/
theorem retainedFieldPrior_coefficient
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K)
    (B : Type u) [CommRing B] [Algebra S B] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] K) (q : B)
    (hq : e ((1 : K) ⊗ₜ[S] q) =
      Coalgebra.counit (R := K) (A := G.coordinateAlgebra)
        (DeterminantSection.positiveDetCoefficient G))
    (φ : B →+* L) (N : ℕ) :
    (fieldTwistedPrior (p := p) base).app ⊤
      ((Scheme.ΓSpecIso (.of L)).inv ((φ q) ^ N)) = (1 : Γ(Spec (.of L), ⊤)) := by
  have hq1 := DeterminantSection.retainedDetCoefficient_unit G S B e q hq
  rw [hq1, map_one, one_pow, map_one]
  exact fieldTwistedPrior_one (p := p) base

end Field
/-- A scheme isomorphic to the spectrum of a field admits a normalized
unit-line functional over any chosen ground-field structure map. -/
theorem point_unit_functional (κ : Type u) [κComm : CommRing κ]
    (hκField : IsField κ) (C : Type u) [cField : Field C] [cκAlg : Algebra C κ]
    (p : ℕ) [cChar : ExpChar C p] (X : Scheme.{u})
    (b : X ⟶ Spec (@CommRingCat.of κ κComm)) [IsIso b]
    (base : X ⟶ Spec (.of C)) :
    ∃ Theta : @frobeniusRestriction.{u} C (@Field.toCommRing C cField) p cChar X
      base (SheafOfModules.unit X.ringCatSheaf) ⟶ SheafOfModules.unit X.ringCatSheaf,
      Theta.app ⊤ (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤)) := by
  let κField : Field κ := hκField.toField
  let κChar : ExpChar κ p :=
    expChar_of_injective_algebraMap (R := C) (A := κ) (algebraMap C κ).injective p
  let sigma : SchemeSplitting X p :=
    (@fieldSplitting.{u} κ κField p κChar).pushforward (inv b)
  refine ⟨@RelativeGlue.schemeOperatorHom.{u} C (@Field.toCommRing C cField)
    p cChar X base sigma.toOperator, ?_⟩
  exact (sigma.onOpen ⊤).map_one

end SchubertGeometry.ProjectiveCartier
