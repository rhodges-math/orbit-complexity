import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineChartData
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalCoordinates
import Batteries.Tactic.OpenPrivate

/-! # The generator and chart squares for affine pullback -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions
universe u

open private chart_adjoint_embed from
  OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineChartData

/- The explicit transpose that `adjointGenerator_exists` constructs, over arbitrary categories,
and its generator square. The chart map below is this transpose at the affine chart, rather than
a choice from `projectiveAffineChartData`: a data declaration containing that concrete
existential exhausts the kernel's memory. The square takes the map `T` with its defining
equation, so the kernel compares `T` with the transpose as a whole; inside `≫` it would first
unfold the composition and then evaluate both maps at the projective line. -/
private noncomputable def adjointTranspose {C : Type*} {D : Type*} [Category C] [Category D]
    {F : C ⥤ C} {H : C ⥤ D} {K : D ⥤ D} {P : D ⥤ C}
    (N : F ⋙ H ⟶ H ⋙ K) {A : D} (uf : K.obj A ⟶ A) (adj : H ⊣ P) {M : C}
    (v : H.obj M ⟶ A) : F.obj M ⟶ P.obj A :=
  adj.homEquiv (F.obj M) A (N.app M ≫ K.map v ≫ uf)

private theorem generator_square {C : Type*} {D : Type*} [Category C] [Category D]
    {F : C ⥤ C} {H : C ⥤ D} {K : D ⥤ D} {P : D ⥤ C}
    {N : F ⋙ H ⟶ H ⋙ K} {O : C} {A : D}
    {r : H.obj O ⟶ A} {ua : F.obj O ⟶ O} {uf : K.obj A ⟶ A}
    (hu : N.app O ≫ K.map r ≫ uf = H.map ua ≫ r)
    (adj : H ⊣ P) {M : C} (v : H.obj M ⟶ A) (i : M ⟶ P.obj A)
    (hi : adj.homEquiv M A v = i) (T : F.obj M ⟶ P.obj A) (hT : T = adjointTranspose N uf adj v)
    (s t : O ⟶ M) (x y : A ⟶ A)
    (hs : H.map s ≫ v = r ≫ x) (ht : H.map t ≫ v = r ≫ y)
    (hx : K.map x ≫ uf = uf ≫ y) :
    F.map s ≫ T = (ua ≫ t) ≫ i := by
  rw [hT, ← hi]
  exact adjunctionGenerator_square adj (F.map s) (ua ≫ t) _ v
    (unitGenerator_square hu v s t x y hs ht hx)

private theorem spec_polynomial_apply (R : Type u) [CommRing R]
    (e : Polynomial R →+* Polynomial R) (r : Polynomial R) :
    (Spec.map (CommRingCat.ofHom e)).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (e r) :=
  (congrArg (fun h => h r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm

private theorem coordinate_power (R : Type u) [CommRing R] (c : Rˣ) (b : R) (d : ℕ) :
    (projectiveAffineCoordinate R c b).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X ^ d)) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        ((Polynomial.C (c : R) * Polynomial.X + Polynomial.C b) ^ d) := by
  change (Spec.map (CommRingCat.ofHom
    (Polynomial.algEquivCMulXAddC (c : R) 0).toRingHom)).appTop
      ((Spec.map (CommRingCat.ofHom
        (Polynomial.algEquivAevalXAddC b).toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X ^ d))) = _
  rw [spec_polynomial_apply, spec_polynomial_apply]
  congr 1
  simp [Polynomial.algEquivAevalXAddC_apply, Polynomial.algEquivCMulXAddC_apply]

private theorem pullback_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules) (u : (Scheme.Modules.pullback f).obj M ⟶ N)
    (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) (h : f.appTop r = s) :
    (Scheme.Modules.pullback f).map (Scheme.Modules.globalSectionsSmul M r) ≫ u =
      u ≫ Scheme.Modules.globalSectionsSmul N s :=
  (congrArg (fun m => m ≫ u) (Scheme.Modules.pullback_map_globalSectionsSmul f M r)).trans
    ((Scheme.Modules.globalSectionsSmul_naturality u (f.appTop r)).trans
      (congrArg (fun q => u ≫ Scheme.Modules.globalSectionsSmul N q) h))

/-- Adjunction turns the proved local pullback comparison into a global map to chart pushforward. -/
def projectiveAffineChartTarget (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).obj
      (SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) ⟶
      (Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩)).obj
        ((SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)) :=
  adjointTranspose
    (C := (projectiveScheme R (ULift.{u} (Fin 2))).Modules)
    (D := (Spec (.of (Polynomial R))).Modules)
    (F := Scheme.Modules.pullback (projectiveAffineMorphism R c b))
    (H := Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩))
    (K := Scheme.Modules.pullback (X := Spec (.of (Polynomial R)))
      (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b))
    (P := Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩))
    (restrictPullbackIso (projectiveLinePolynomialChart R ⟨0⟩)
      (projectiveAffineCoordinate R c b) (projectiveAffineMorphism R c b)
      (projectiveAffineCoordinate_chart R c b)).hom
    (A := SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (structurePullbackUnit (projectiveAffineCoordinate R c b))
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩))
    (M := SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d)
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom

/-- A section square follows from its two polynomial-chart coefficients. -/
theorem projectiveAffineSection_square (R : Type u) [CommRing R] (d : ℕ) (c : Rˣ) (b : R)
    (s t : (SheafOfModules.unit (projectiveScheme R (ULift.{u} (Fin 2))).ringCatSheaf) ⟶
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d) (x y : Polynomial R)
    (hs : (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map s ≫
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (X := Spec (.of (Polynomial R))) ((SheafOfModules.unit
          (Spec (.of (Polynomial R))).ringCatSheaf))
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv x))
    (ht : (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩)).map t ≫
        (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom ≫
        Scheme.Modules.globalSectionsSmul (X := Spec (.of (Polynomial R))) ((SheafOfModules.unit
          (Spec (.of (Polynomial R))).ringCatSheaf))
          ((Scheme.ΓSpecIso (.of (Polynomial R))).inv y))
    (hxy : (projectiveAffineCoordinate R c b).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv x) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv y) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map s ≫ projectiveAffineChartTarget R
      d c b =
      ((Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫ t) ≫
        projectiveTransitionEmbed R d :=
by
  have hx := pullback_scalar (X := Spec (.of (Polynomial R)))
    (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b)
    ((SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf))
    ((SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf))
    (structurePullbackUnit (X := Spec (.of (Polynomial R)))
      (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b)) _ _ hxy
  have h := generator_square
    (C := (projectiveScheme R (ULift.{u} (Fin 2))).Modules)
    (D := (Spec (.of (Polynomial R))).Modules)
    (F := Scheme.Modules.pullback (projectiveAffineMorphism R c b))
    (H := Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart R ⟨0⟩))
    (K := Scheme.Modules.pullback (X := Spec (.of (Polynomial R)))
      (Y := Spec (.of (Polynomial R))) (projectiveAffineCoordinate R c b))
    (P := Scheme.Modules.pushforward (projectiveLinePolynomialChart R ⟨0⟩))
    (N := (restrictPullbackIso (projectiveLinePolynomialChart R ⟨0⟩)
      (projectiveAffineCoordinate R c b) (projectiveAffineMorphism R c b)
      (projectiveAffineCoordinate_chart R c b)).hom)
    (O := SheafOfModules.unit (projectiveScheme R (ULift.{u} (Fin 2))).ringCatSheaf)
    (A := SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)
    (r := (Scheme.Modules.restrictUnitIso (projectiveLinePolynomialChart R ⟨0⟩)).hom)
    (ua := structurePullbackUnit (projectiveAffineMorphism R c b))
    (uf := structurePullbackUnit (projectiveAffineCoordinate R c b))
    (projectiveAffineUnit R c b)
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart R ⟨0⟩))
    (M := SchubertGeometry.ProjectiveLine.projectiveTransitionModule R d)
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart R d ⟨0⟩).hom
    (projectiveTransitionEmbed R d) (chart_adjoint_embed R d) (projectiveAffineChartTarget R d c b)
      rfl
    s t
    (Scheme.Modules.globalSectionsSmul (X := Spec (.of (Polynomial R)))
      ((SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)) ((Scheme.ΓSpecIso (.of
        (Polynomial R))).inv x))
    (Scheme.Modules.globalSectionsSmul (X := Spec (.of (Polynomial R)))
      ((SheafOfModules.unit (Spec (.of (Polynomial R))).ringCatSheaf)) ((Scheme.ΓSpecIso (.of
        (Polynomial R))).inv y))
    hs ht hx
  exact h.trans (congrArg (fun u => (u ≫ t) ≫ projectiveTransitionEmbed R d)
    (structurePullbackUnit_eq (projectiveAffineMorphism R c b)).symm)

private theorem coproduct_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U M : C} [HasBinaryCoproduct U U]
    [HasBinaryCoproduct (F.obj U) (F.obj U)] [PreservesColimit (pair U U) F]
    (s₀ s₁ : U ⟶ M) {N V : D} (t₀ t₁ : F.obj U ⟶ N)
    (a : F.obj M ⟶ V) (e : N ⟶ V)
    (h₀ : F.map s₀ ≫ a = t₀ ≫ e) (h₁ : F.map s₁ ≫ a = t₁ ≫ e) :
    F.map (coprod.desc s₀ s₁) ≫ a =
      ((PreservesColimitPair.iso F U U).inv ≫ coprod.desc t₀ t₁) ≫ e := by
  apply (cancel_epi (PreservesColimitPair.iso F U U).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simpa only [PreservesColimitPair.iso_hom, coprodComparison_inl_assoc,
      ← Functor.map_comp_assoc, coprod.inl_desc, coprod.inl_desc_assoc] using h₀
  · simpa only [PreservesColimitPair.iso_hom, coprodComparison_inr_assoc,
      ← Functor.map_comp_assoc, coprod.inr_desc, coprod.inr_desc_assoc] using h₁

/-- The constant generator satisfies the scalar pullback square. -/
private theorem generator_zero_square (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map
        (projectiveMonomialSection R d 0 (Nat.zero_le _)) ≫
        projectiveAffineChartTarget R d c b =
      ((Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫
        projectiveMonomialSection R d 0 (Nat.zero_le _)) ≫
        projectiveTransitionEmbed R d := by
  exact projectiveAffineSection_square R d c b _ _ (Polynomial.X ^ 0) (Polynomial.X ^ 0)
    (projectiveMonomial_left R d 0 (Nat.zero_le _))
    (projectiveMonomial_left R d 0 (Nat.zero_le _)) (by simp only [pow_zero, map_one])

/-- The endpoint generator satisfies the scalar pullback square. -/
private theorem generator_endpoint_square (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map
        (projectiveMonomialSection R d d le_rfl) ≫
        projectiveAffineChartTarget R d c b =
      ((Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫
        projectiveAffineEndpoint R d (c : R) b) ≫ projectiveTransitionEmbed R d := by
  exact projectiveAffineSection_square R d c b _ _ (Polynomial.X ^ d)
    ((Polynomial.C (c : R) * Polynomial.X + Polynomial.C b) ^ d)
    (projectiveMonomial_left R d d le_rfl) (projectiveAffineEndpoint_left R d (c : R) b)
    (coordinate_power R c b d)

/-- Pullback of the two-generator evaluation has the required global chart square. -/
theorem projectiveAffineGenerator_square (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map (projectiveOrdinaryEval R d) ≫
        projectiveAffineChartTarget R d c b =
      projectiveAffineGeneratorMap R d c b ≫ projectiveTransitionEmbed R d := by
  exact coproduct_square (Scheme.Modules.pullback (projectiveAffineMorphism R c b)) _ _ _ _
    (projectiveAffineChartTarget R d c b) (projectiveTransitionEmbed R d)
    (generator_zero_square R d c b) (generator_endpoint_square R d c b)



end SchubertGeometry.ProjectiveLine
