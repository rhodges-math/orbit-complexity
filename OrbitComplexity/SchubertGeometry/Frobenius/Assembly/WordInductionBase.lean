import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPointModel
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The empty prefix of word induction

The empty word retains the arithmetic point, identity endpoint, unit
coefficient and empty boundary family. Its matching section normalizes a
functional on every prescribed field fibre.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private coefficientRing coefficientRing_fg coefficientRing_two
  pointDiagram pointDiagram_fp pointDiagram_smooth pointDiagram_open pointDiagram_directed
  pointCocone pointCoconeColimit pointCocone_proper pointCocone_smooth pointCocone_connected
  pointComparison_value pointComparison_right pointCoefficientMap
  emptyToSpec pointEndpoint pointEndpoint_flag unit_coefficient pointFibre_isIso
  pointSection_isIso functional_of_unit quadratic_coeff_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPointModel

namespace SchubertGeometry.RetainedCharacter

private def pointPrefixModel {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero :
    CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K) (hS : S.FG) (hTwo : IsUnit (2 : S)) :
    PrefixModel G [] where
  S := S
  hS := hS
  twoUnit := hTwo
  J := PUnit.{u+1}
  finite := inferInstance
  F := (@pointDiagram.{u} K (@Field.toCommRing K kField))
  N := (@pointDiagram.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
      kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S))
  e _ := Algebra.TensorProduct.rid S K K
  he := by
    intro s t f
    ext
  fOpen := (@pointDiagram_open.{u} K (@Field.toCommRing K kField))
  fDir := (@pointDiagram_directed.{u} K (@Field.toCommRing K kField))
  nOpen := (@pointDiagram_open.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
      K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S))
  nDir := (@pointDiagram_directed.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S))
  fp := (@pointDiagram_fp.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
      kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S))
  smooth := (@pointDiagram_smooth.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S))
  sel s := ⟨PUnit.unit, by
    obtain ⟨j, hj⟩ := s.property
    exact (Subsingleton.elim j PUnit.unit) ▸ hj⟩
  b := ((@pointCocone.{u} K (@Field.toCommRing K kField)) (bsdhToSpec G []) ((@emptyToSpec.{u} K
      kField kClosed kZero G))).ι
  hb := (@pointCoconeColimit.{u} K (@Field.toCommRing K kField)) (bsdhToSpec G [])
      ((@emptyToSpec.{u} K kField kClosed kZero G))
  cG := (@pointCocone.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K
      kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S))
      (𝟙 _) rfl
  hcG := (@pointCoconeColimit.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
      K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S))
      (𝟙 _) rfl
  m₀ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  hm₀ := by
    change IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (bsdhToSpec G []) (𝟙 _) _
    rw [emptyToSpec]
    exact IsPullback.id_vert _
  hbmodel := by
    intro s
    change (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)) =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.rid S K K).toRingHom.comp
        (@Algebra.TensorProduct.includeRight S K S _ _ _ _ _).toRingHom)) ≫ 𝟙 _
    rw [pointComparison_right]
    simp only [Category.id_comp, Category.comp_id]
  proper := (@pointCocone_proper.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S))
  smoothModel := (@pointCocone_smooth.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S))
  connected := (@pointCocone_connected.{u} S (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S))
  point _ := 1
  a := (@pointEndpoint.{u} K kField kClosed kZero G)
  ha := by
    intro j
    change ((@pointEndpoint.{u} K kField kClosed kZero G j)).left ≫ (flagChartMorphism G 1).left =
      (𝟙 _) ≫ (𝟙 _ ≫ bsdhMap G [])
    simpa only [Category.id_comp] using (@pointEndpoint_flag.{u} K kField kClosed kZero G j)
  beta _ _ _ _ _ := 1
  hgroup := by
    intro s j hj k hk
    rw [MonObj.one_comp, mul_one]
  hnatural := by
    intro s t f j hj k hk
    exact (MonObj.comp_one _).symm
  hbeta := by
    intros
    exact (one_mul (1 : _)).symm
  v := (@pointCoefficientMap.{u} S K (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
      K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
      (@Field.toCommRing K kField) (@Subalgebra.toAlgebra K ℤ K Int.instCommSemiring
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField)) (@CommSemiring.toSemiring K
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) (@Ring.toIntAlgebra K
      (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id K
      (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) S))
  hv _ := Subtype.val_injective
  eValue _ := (@pointComparison_value.{u} S K (@Subalgebra.toCommRing ℤ K Int.instCommRing
      (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
      (@Field.toDivisionRing K kField))) S) (@Field.toCommRing K kField) (@Subalgebra.toAlgebra K ℤ
      K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
      (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) (@Algebra.id
      K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) S))
  delta _ _ _ _ _ := 1
  hdelta := by
    intro s j hj k hk
    exact (map_one (((@pointCoefficientMap.{u} S K (@Subalgebra.toCommRing ℤ K Int.instCommRing
        (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) (@Field.toCommRing K kField) (@Subalgebra.toAlgebra K
        ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) S))).app
        s).hom).trans
      (congrArg Units.val (map_one
        (ProjectiveLine.positiveBorelSection G (((@pointDiagram.{u} K (@Field.toCommRing K
            kField))).obj s)))).symm
  hco := by
    intros
    exact (one_mul (1 : _)).symm
  hn := by
    intros
    exact map_one _
  P _ := Polynomial.X ^ 2
  hP _ := Polynomial.natDegree_X_pow_le 2
  hr := by
    intros
    exact (mul_one _).symm
  hCoefficient := by
    intro j
    exact (quadratic_coeff_map (((@pointCoefficientMap.{u} S K (@Subalgebra.toCommRing ℤ K
        Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
        (@Field.toDivisionRing K kField))) S) (@Field.toCommRing K kField) (@Subalgebra.toAlgebra K
        ℤ K Int.instCommSemiring (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K kField))) S))).app
        (singletonIndex j)).hom).trans
      (@unit_coefficient.{u} K kField kClosed kZero G j).symm
  boundaries := Fin.elim0
  hclosed := fun k => Fin.elim0 k
  nB := fun k => Fin.elim0 k
  hnB := fun k => Fin.elim0 k

private theorem pointPrefixModel_splits {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K]
    [kZero : CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K) (hS : S.FG)
    (hTwo : IsUnit (2 : S)) :
    PrefixSplits (@pointPrefixModel.{u} K kField kClosed kZero G S hS hTwo) := by
  intro κ κComm hκField C cField cκAlg p cChar cPerfect hp hp'
    coefficientMap X baseκ x hx B bD hB L sectionHom
  have hb : IsIso baseκ := pointFibre_isIso x baseκ coefficientMap hx
  have hs : IsIso sectionHom :=
    @pointSection_isIso.{u} S
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          S)
      (@pointPrefixModel.{u} K kField kClosed kZero G S hS hTwo).delta (@pointPrefixModel.{u} K
          kField kClosed kZero G S hS hTwo).hco (@pointPrefixModel.{u} K kField kClosed kZero G S hS
          hTwo).hn
      (fun j => ((@pointPrefixModel.{u} K kField kClosed kZero G S hS hTwo).P (singletonIndex
          j)).coeff 2)
      (@pointPrefixModel.{u} K kField kClosed kZero G S hS hTwo).hr (fun _ =>
          Polynomial.coeff_X_pow_self 2) ((p - 1) / 2)
  obtain ⟨Theta, hTheta⟩ := @ProjectiveCartier.point_unit_functional.{u}
    κ κComm hκField C cField cκAlg p cChar X baseκ hb
    (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
  have hsX : IsIso (@pullSection.{u} X (@pointPrefixModel.{u} K kField kClosed kZero G S hS
      hTwo).cG.pt.left x L sectionHom) :=
    IsIso.comp_isIso' (Scheme.Modules.pullbackObjUnitIso x).isIso_inv
      (@Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pullback x) sectionHom hs)
  let E := @asIso X.Modules (inferInstanceAs (Category.{u} X.Modules))
    (SheafOfModules.unit X.ringCatSheaf) ((Scheme.Modules.pullback x).obj L)
    (@pullSection.{u} X (@pointPrefixModel.{u} K kField kClosed kZero G S hS hTwo).cG.pt.left x L
        sectionHom) hsX
  obtain ⟨Phi, hPhi⟩ := @functional_of_unit.{u} C (@Field.toCommRing C cField)
    p cChar X (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
    ((Scheme.Modules.pullback x).obj L)
    (@pullSection.{u} X (@pointPrefixModel.{u} K kField kClosed kZero G S hS hTwo).cG.pt.left x L
        sectionHom)
    E.inv E.hom_inv_id Theta hTheta
  exact ⟨Phi, hPhi, fun k => Fin.elim0 k⟩


/-- The singleton arithmetic point, unit coefficient and identity endpoint
form the prefix model of the empty word. -/
def emptyPrefix {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) : PrefixModel G [] :=
  @pointPrefixModel.{u} K kField kClosed kZero G
    (@coefficientRing.{u} K kField)
    (@coefficientRing_fg.{u} K kField) (@coefficientRing_two.{u} K kField kZero)

/-- Every field fibre of the empty prefix has a normalized functional;
there are no omitted-letter boundaries in the empty word. -/
theorem emptyPrefix_splits {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero :
    CharZero K]
    (G : ReductiveGroupData K) : PrefixSplits (emptyPrefix G) :=
  @pointPrefixModel_splits.{u} K kField kClosed kZero G
    (@coefficientRing.{u} K kField)
    (@coefficientRing_fg.{u} K kField) (@coefficientRing_two.{u} K kField kZero)

end SchubertGeometry.RetainedCharacter
