import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBaseNormalization
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingInduction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The constant arithmetic point and its matching section

A singleton coefficient diagram has its prescribed point as colimit.
Its unit coefficient gives an invertible matching section on every power.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private empty_unit_endpoint from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBaseNormalization
open private prior_map_normalized from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingInduction
open private twistModuleMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

namespace SchubertGeometry.RetainedCharacter
private theorem pointIndex_eq (s t : {s : Finset PUnit.{u+1} // s.Nonempty}) : s = t := by
  apply Subtype.ext
  apply Finset.ext
  intro j
  constructor
  · intro _
    obtain ⟨k, hk⟩ := t.property
    exact (Subsingleton.elim k j) ▸ hk
  · intro _
    obtain ⟨k, hk⟩ := s.property
    exact (Subsingleton.elim k j) ▸ hk
private def pointDiagram (R : Type u) [CommRing R] :
    {s : Finset PUnit.{u+1} // s.Nonempty} ⥤ CommAlgCat.{u} R :=
  (Functor.const _).obj (.of R R)
private def pointCocone (R : Type u) [CommRing R]
    (base : Spec (.of R) ⟶ Spec (.of R)) (hbase : base = 𝟙 _) :
    Cocone ((pointDiagram R).op ⋙ algSpec (.of R)) :=
  @Cocone.mk.{u,u,u,u+1}
    {s : Finset PUnit.{u+1} // s.Nonempty}ᵒᵖ
    (inferInstanceAs (Category.{u} {s : Finset PUnit.{u+1} // s.Nonempty}ᵒᵖ))
    (Over (Spec (.of R))) (inferInstanceAs (Category.{u} (Over (Spec (.of R)))))
    ((pointDiagram R).op ⋙ algSpec (.of R)) (Over.mk base)
    { app := fun _ => Over.homMk (𝟙 (Spec (.of R))) (by
        change (𝟙 _) ≫ base = Spec.map (CommRingCat.ofHom (algebraMap R R))
        rw [Category.id_comp, hbase, Algebra.algebraMap_self]
        change (𝟙 _) = Spec.map (𝟙 (.of R))
        simp only [Spec.map_id])
      naturality := by
        intro s t f
        apply (Over.forget (Spec (.of R))).map_injective
        change Spec.map (𝟙 (.of R)) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        simp only [Spec.map_id, Category.id_comp] }
private def oneObjectColimit {I : Type u} [Category.{u} I]
    {D : Type (u+1)} [Category.{u} D] (F : I ⥤ D) (c : Cocone F) (sub : ∀ i j : I, i = j) (i : I)
    [IsIso (c.ι.app i)] : IsColimit c where
  desc s := inv (c.ι.app i) ≫ s.ι.app i
  fac s j := by
    cases sub j i
    simp only [IsIso.hom_inv_id_assoc]
  uniq s m hm := by
    apply (cancel_epi (c.ι.app i)).1
    simpa only [IsIso.hom_inv_id_assoc] using hm i
private def pointCoconeColimit (R : Type u) [CommRing R]
    (base : Spec (.of R) ⟶ Spec (.of R)) (hbase : base = 𝟙 _) :
    IsColimit (pointCocone R base hbase) := by
  let c := pointCocone R base hbase
  let s : {s : Finset PUnit.{u+1} // s.Nonempty} := singletonIndex PUnit.unit
  let : IsIso ((Over.forget (Spec (.of R))).map (c.ι.app (op s))) := by
    change IsIso (𝟙 (Spec (.of R)))
    infer_instance
  let : IsIso (c.ι.app (op s)) :=
    isIso_of_reflects_iso (c.ι.app (op s)) (Over.forget (Spec (.of R)))
  exact oneObjectColimit _ c
    (fun i j => congrArg op (pointIndex_eq i.unop j.unop)) (op s)
private theorem oneObjectDirected {I : Type u} [Category.{u} I]
    [Quiver.IsThin I] (sub : ∀ i j : I, i = j) (F : I ⥤ Type v) : F.IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj h
  cases sub j i
  cases sub k i
  have hfi : fi = 𝟙 _ := Subsingleton.elim _ _
  have hfj : fj = 𝟙 _ := Subsingleton.elim _ _
  rw [hfi, hfj] at h
  have hi (x : F.obj i) : F.map (𝟙 i) x = x :=
    ConcreteCategory.congr_hom (F.map_id i) x
  exact ⟨i, 𝟙 _, 𝟙 _, xi, hi xi, (hi xi).trans ((hi xi).symm.trans (h.trans (hi xj)))⟩
private theorem pointDiagram_open (R : Type u) [CommRing R]
    {s t : {s : Finset PUnit.{u+1} // s.Nonempty}} (f : s ⟶ t) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((pointDiagram R).map f).hom.toRingHom)) := by
  change IsOpenImmersion (Spec.map (𝟙 (.of R)))
  rw [Spec.map_id]
  infer_instance

private theorem pointDiagram_directed (R : Type u) [CommRing R] :
    (((pointDiagram R).op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected :=
  oneObjectDirected (fun i j => congrArg op (pointIndex_eq i.unop j.unop)) _

private def pointCoefficientMap (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] :
    pointDiagram R ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      pointDiagram K ⋙ forget₂ (CommAlgCat K) CommRingCat where
  app _ := CommRingCat.ofHom (algebraMap R K)
  naturality _ _ _ :=
    (Category.id_comp (CommRingCat.ofHom (algebraMap R K))).trans
      (Category.comp_id (CommRingCat.ofHom (algebraMap R K))).symm

private theorem pointComparison_value (R K : Type u) [CommRing R] [CommRing K]
    [Algebra R K] (x : R) :
    Algebra.TensorProduct.rid R K K ((1 : K) ⊗ₜ[R] x) = algebraMap R K x := by
  simp only [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

private def coefficientRing (K : Type u) [Field K] : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({(2 : K)⁻¹} : Set K)

private theorem coefficientRing_fg (K : Type u) [Field K] : (coefficientRing K).FG := by
  simpa only [coefficientRing, Finset.coe_singleton] using
    Subalgebra.fg_adjoin_finset (R := ℤ) ({(2 : K)⁻¹} : Finset K)

private theorem coefficientRing_two (K : Type u) [Field K] [CharZero K] :
    IsUnit (2 : coefficientRing K) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(2 : K)⁻¹, Algebra.subset_adjoin (by simp only [Set.mem_singleton_iff])⟩, ?_⟩
  apply Subtype.ext
  change (2 : K) * (2 : K)⁻¹ = 1
  exact mul_inv_cancel₀ two_ne_zero

private theorem pointDiagram_fp (R : Type u) [CommRing R]
    (s : {s : Finset PUnit.{u+1} // s.Nonempty}) :
    Algebra.FinitePresentation R ((pointDiagram R).obj s) := by
  change Algebra.FinitePresentation R R
  infer_instance

private theorem pointDiagram_smooth (R : Type u) [CommRing R]
    (s : {s : Finset PUnit.{u+1} // s.Nonempty}) :
    Algebra.Smooth R ((pointDiagram R).obj s) := by
  change Algebra.Smooth R R
  infer_instance

private theorem pointCocone_proper (R : Type u) [CommRing R] :
    IsProper (pointCocone R (𝟙 _) rfl).pt.hom := by
  change IsProper (𝟙 (Spec (.of R)))
  infer_instance

private theorem pointCocone_smooth (R : Type u) [CommRing R] :
    Smooth (pointCocone R (𝟙 _) rfl).pt.hom := by
  change Smooth (𝟙 (Spec (.of R)))
  infer_instance

private theorem pointCocone_connected (R : Type u) [CommRing R] :
    GeometricallyConnected (pointCocone R (𝟙 _) rfl).pt.hom := by
  change GeometricallyConnected (𝟙 (Spec (.of R)))
  constructor
  intro L _ t Z fst snd h
  let : IsIso snd := h.isIso_snd_of_isIso
  exact snd.homeomorph.connectedSpace_iff.mpr inferInstance

private def pointOverMap (R : Type u) [rComm : CommRing R]
    (A : Over (Spec (.of R))) {X : Over (Spec (.of R))}
    (f : Spec (.of R) ⟶ X.left) (hf : f ≫ X.hom = 𝟙 _) : A ⟶ X :=
  Over.homMk (A.hom ≫ f) (by rw [Category.assoc, hf, Category.comp_id])

private theorem quadratic_coeff_map {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : f (((Polynomial.X : Polynomial R) ^ 2).coeff 2) = 1 :=
  (congrArg f (Polynomial.coeff_X_pow_self 2)).trans (map_one f)

private theorem preimage_factor_one {A B R : CommRingCat.{u}}
    (f : Spec B ⟶ Spec A) (t : Spec B ⟶ Spec R) (e : Spec R ⟶ Spec A)
    (h : f = t ≫ e) (x : A) (hx : (Spec.preimage e).hom x = 1) :
    (Spec.preimage f).hom x = 1 := by
  rw [h, Spec.preimage_comp]
  exact (congrArg (Spec.preimage t).hom hx).trans (map_one (Spec.preimage t).hom)

private theorem pointOverMap_comp (R : Type u) [rComm : CommRing R]
    (A : Over (Spec (.of R))) {X Y : Over (Spec (.of R))}
    (f : Spec (.of R) ⟶ X.left) (hf : f ≫ X.hom = 𝟙 _) (g : X ⟶ Y) :
    (@pointOverMap.{u} R rComm A X f hf ≫ g).left = A.hom ≫ (f ≫ g.left) :=
  Category.assoc _ _ _

private theorem pointDiagram_hom_comp (R : Type u) [rComm : CommRing R]
    (j : PUnit.{u+1}) {X : Scheme.{u}} (f : Spec (.of R) ⟶ X) :
    ((algSpec (.of R)).obj (op ((@pointDiagram.{u} R rComm).obj
      (singletonIndex j)))).hom ≫ f = f := by
  change Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ f = f
  rw [Algebra.algebraMap_self]
  exact (congrArg (fun q => q ≫ f) (Spec.map_id (.of R))).trans (Category.id_comp f)

private theorem pointComparison_right (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] :
    (Algebra.TensorProduct.rid R K K).toRingHom.comp
      (@Algebra.TensorProduct.includeRight R K R _ _ _ _ _).toRingHom = algebraMap R K := by
  ext x
  exact pointComparison_value R K x

private theorem endpoint_triangle {D : Type (u+1)} [Category.{u} D]
    {P U V W : D} (a : P ⟶ U) (c : U ⟶ V) (q : V ⟶ W)
    (r : P ⟶ V) (e : P ⟶ W) (z : U ⟶ W)
    (hc : c ≫ q = z) (ha : a ≫ c = r) (he : r ≫ q = e) : a ≫ z = e :=
  (congrArg (fun f => a ≫ f) hc.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ q) ha).trans he))

private theorem section_isIso_of_frame {D : Type (u+1)} [Category.{u} D]
    (F : D ⥤ D) (alpha : F ≅ 𝟭 D) {U M : D}
    (e : F.obj U ≅ U) (s : U ⟶ M) (E : F.obj M ≅ U)
    (h : (e.inv ≫ F.map s) ≫ E.hom = 𝟙 U) : IsIso s := by
  let : IsIso (e.inv ≫ F.map s) := IsIso.of_isIso_fac_right h
  have hm : IsIso (F.map s) := IsIso.of_isIso_comp_left e.inv (F.map s)
  exact (NatIso.isIso_map_iff alpha s).mp hm

private theorem pointSection_isIso (R : Type u) [rComm : CommRing R]
    (delta : ∀ (s : {s : Finset PUnit.{u+1} // s.Nonempty})
      (j : PUnit.{u+1}) (_ : j ∈ s.val) (k : PUnit.{u+1}) (_ : k ∈ s.val),
      ((pointDiagram R).obj s)ˣ)
    (hco : ∀ s j hj k hk l hl, delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((pointDiagram R).map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (r : ∀ j : PUnit.{u+1}, (pointDiagram R).obj (singletonIndex j))
    (hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      ((pointDiagram R).map (singletonArrow s j hj)).hom (r j) =
        ((pointDiagram R).map (singletonArrow s k hk)).hom (r k) *
          (delta s j hj k hk : (pointDiagram R).obj s))
    (hr1 : ∀ j, r j = 1) (n : ℕ) :
    IsIso (@coefficientMatchingSection.{u} R PUnit.{u+1} rComm
      (pointDiagram R) (pointCocone R (𝟙 _) rfl) delta r hr n) := by
  let E := @retainedUnitFrame.{u} R PUnit.{u+1} rComm
    (pointDiagram R) (@pointDiagram_open.{u} R rComm) (@pointDiagram_directed.{u} R rComm)
    (pointCocone R (𝟙 _) rfl) (pointCoconeColimit R (𝟙 _) rfl) delta n hco hn PUnit.unit 1
  have hs := @retainedUnitFrame_section.{u} R PUnit.{u+1} rComm
    (pointDiagram R) (@pointDiagram_open.{u} R rComm) (@pointDiagram_directed.{u} R rComm)
    (pointCocone R (𝟙 _) rfl) (pointCoconeColimit R (𝟙 _) rfl) delta n hco hn r hr PUnit.unit 1
  have hv : (r PUnit.unit * (1 : (pointDiagram R).obj (singletonIndex PUnit.unit))) ^ n = 1 := by
    rw [hr1, one_mul, one_pow]
  have hScalar : Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of ((pointDiagram R).obj (singletonIndex PUnit.unit)))).inv
        ((r PUnit.unit * 1) ^ n)) = 𝟙 _ :=
    (congrArg (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of R)).ringCatSheaf))
      ((congrArg (fun a => (Scheme.ΓSpecIso
        (.of ((pointDiagram R).obj (singletonIndex PUnit.unit)))).inv a) hv).trans
          (map_one (Scheme.ΓSpecIso
            (.of ((pointDiagram R).obj (singletonIndex PUnit.unit)))).inv.hom))).trans
      (ProjectiveCartier.RelativeGlue.globalSmul_one (SheafOfModules.unit (Spec (.of
          R)).ringCatSheaf))
  exact @section_isIso_of_frame.{u} (Spec (.of R)).Modules
    (inferInstanceAs (Category.{u} (Spec (.of R)).Modules))
    (Scheme.Modules.pullback (𝟙 (Spec (.of R))))
    (Scheme.Modules.pullbackId (Spec (.of R)))
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)
    (@matchingModule.{u} R PUnit.{u+1} rComm (pointDiagram R)
      (pointCocone R (𝟙 _) rfl) delta n)
    (Scheme.Modules.pullbackObjUnitIso (𝟙 (Spec (.of R))))
    (@coefficientMatchingSection.{u} R PUnit.{u+1} rComm (pointDiagram R)
      (pointCocone R (𝟙 _) rfl) delta r hr n) E (hs.trans hScalar)

private theorem pointFibre_isIso {X Y Z : Scheme.{u}}
    (x : X ⟶ Z) (b : X ⟶ Y) (c : Y ⟶ Z)
    (h : IsPullback x b (𝟙 Z) c) : IsIso b := by
  rw [← h.isoPullback_hom_snd]
  infer_instance

private theorem functional_of_unit {C : Type u} [cComm : CommRing C]
    {p : ℕ} [cChar : ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (e : M ⟶ SheafOfModules.unit X.ringCatSheaf) (hs : s ≫ e = 𝟙 _)
    (Theta : @frobeniusRestriction.{u} C cComm p cChar X base
      (SheafOfModules.unit X.ringCatSheaf) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hTheta : Theta.app ⊤ (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤))) :
    ∃ Phi : @frobeniusRestriction.{u} C cComm p cChar X base M ⟶
        SheafOfModules.unit X.ringCatSheaf,
      Phi.app ⊤ (@Scheme.Modules.Hom.app.{u} X
        (SheafOfModules.unit X.ringCatSheaf) M s ⊤ (1 : Γ(X, ⊤))) =
          (1 : Γ(X, ⊤)) := by
  refine ⟨@twistModuleMap.{u} C cComm p cChar X base M
    (SheafOfModules.unit X.ringCatSheaf) e ≫ Theta, ?_⟩
  exact @prior_map_normalized.{u} C cComm p cChar X base M
    (SheafOfModules.unit X.ringCatSheaf) e s (𝟙 _) hs Theta hTheta

section Word

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K)

private theorem unit_chart :
    η[(oppositeUnipotentVariety G).toOver] ≫ flagChartMap G 1 =
      η[(reductiveVariety G).toOver] := by
  have hc : flagChartMap G 1 = oppositeUnipotentInclusion G := by
    apply Variety.mapPoints_injective
    funext p
    rw [flagChartMap_points, oppositeUnipotentInclusion_points, one_mul]
  rw [hc]
  exact IsMonHom.one_hom (oppositeUnipotentInclusion G)

private theorem emptyToSpec : bsdhToSpec G [] = 𝟙 (Spec (.of K)) := (baseFlagPoint G).property

private def pointEndpoint (j : PUnit.{u+1}) :
    (algSpec (.of K)).obj (op ((@pointDiagram.{u} K
      (@Field.toCommRing K kField)).obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver :=
  @pointOverMap.{u} K (@Field.toCommRing K kField)
    ((algSpec (.of K)).obj (op ((@pointDiagram.{u} K
      (@Field.toCommRing K kField)).obj (singletonIndex j))))
    (oppositeUnipotentVariety G).toOver η[(oppositeUnipotentVariety G).toOver].left
    η[(oppositeUnipotentVariety G).toOver].w

private theorem pointEndpoint_flag (j : PUnit.{u+1}) :
    (pointEndpoint G j).left ≫ (flagChartMorphism G 1).left = bsdhMap G [] := by
  have hm := @pointOverMap_comp.{u} K (@Field.toCommRing K kField)
    ((algSpec (.of K)).obj (op ((@pointDiagram.{u} K
      (@Field.toCommRing K kField)).obj (singletonIndex j))))
    (oppositeUnipotentVariety G).toOver (reductiveVariety G).toOver
    η[(oppositeUnipotentVariety G).toOver].left
    η[(oppositeUnipotentVariety G).toOver].w (flagChartMap G 1)
  have hp := @pointDiagram_hom_comp.{u} K (@Field.toCommRing K kField) j (reductiveVariety G).scheme
    (η[(oppositeUnipotentVariety G).toOver].left ≫ (flagChartMap G 1).left)
  exact @endpoint_triangle.{u} Scheme (inferInstanceAs (Category.{u} Scheme))
    (bsdhScheme G []) (oppositeUnipotentVariety G).scheme
    (reductiveVariety G).scheme (flagVariety G).scheme
    (pointEndpoint G j).left (flagChartMap G 1).left (flagQuotient G)
    η[(reductiveVariety G).toOver].left (bsdhMap G []) (flagChartMorphism G 1).left
    (congrArg Over.Hom.left (flagChartMap_quotient G 1))
    (hm.trans (hp.trans
      (congrArg Over.Hom.left (@unit_chart.{u} K kField kClosed kZero G))))
    (@empty_unit_endpoint.{u} K kField kClosed kZero G)

private theorem coefficient_at_unit {K : Type u} [kField : Field K]
    [kClosed : IsAlgClosed K] [kZero : CharZero K] (G : ReductiveGroupData K) :
    (Spec.preimage η[(reductiveVariety G).toOver].left).hom
      (DeterminantSection.positiveDetCoefficient G) = 1 := by
  have hu : η[(reductiveVariety G).toOver].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K G.coordinateAlgebra)) :=
    one_spec_asOver_spec_left
      (R := CommRingCat.of K) (A := CommRingCat.of G.coordinateAlgebra)
  rw [hu, Spec.preimage_map]
  exact DeterminantSection.positiveDet_counit G

private theorem wordCoefficient_factor_one {K : Type u} [kField : Field K]
    [kClosed : IsAlgClosed K] [kZero : CharZero K] (G : ReductiveGroupData K)
    {J : Type u} (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (point : J → G.points) (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (j : J) (t : Spec (.of (F.obj (singletonIndex j))) ⟶ Spec (.of K))
    (h : (a j ≫ flagChartMap G (point j)).left = t ≫ η[(reductiveVariety G).toOver].left) :
    wordRingCoefficient G F point a j = 1 :=
  @preimage_factor_one.{u} (.of G.coordinateAlgebra) (.of (F.obj (singletonIndex j)))
    (.of K) (a j ≫ flagChartMap G (point j)).left t
    η[(reductiveVariety G).toOver].left h (DeterminantSection.positiveDetCoefficient G)
    (@coefficient_at_unit.{u} K kField kClosed kZero G)

private theorem unit_coefficient {K : Type u} [kField : Field K]
    [kClosed : IsAlgClosed K] [kZero : CharZero K] (G : ReductiveGroupData K)
    (j : PUnit.{u+1}) : @wordRingCoefficient.{u} K kField kClosed kZero G PUnit.{u+1}
      (@pointDiagram.{u} K (@Field.toCommRing K kField)) (fun _ => 1)
      (@pointEndpoint.{u} K kField kClosed kZero G) j = 1 := by
  exact @wordCoefficient_factor_one.{u} K kField kClosed kZero G PUnit.{u+1}
    (@pointDiagram.{u} K (@Field.toCommRing K kField)) (fun _ => 1)
    (@pointEndpoint.{u} K kField kClosed kZero G) j
    ((algSpec (.of K)).obj (op ((@pointDiagram.{u} K
      (@Field.toCommRing K kField)).obj (singletonIndex j)))).hom
    ((@pointOverMap_comp.{u} K (@Field.toCommRing K kField)
      ((algSpec (.of K)).obj (op ((@pointDiagram.{u} K
        (@Field.toCommRing K kField)).obj (singletonIndex j))))
      (oppositeUnipotentVariety G).toOver (reductiveVariety G).toOver
      η[(oppositeUnipotentVariety G).toOver].left
      η[(oppositeUnipotentVariety G).toOver].w (flagChartMap G 1)).trans
        (congrArg (fun e => ((algSpec (.of K)).obj
          (op ((@pointDiagram.{u} K (@Field.toCommRing K kField)).obj
            (singletonIndex j)))).hom ≫ e)
          (congrArg Over.Hom.left (@unit_chart.{u} K kField kClosed kZero G))))

end Word
end SchubertGeometry.RetainedCharacter
