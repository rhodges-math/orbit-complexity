import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordRawCharts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarInfinitySplitting
import OrbitComplexity.SchubertGeometry.Normality.Bundles.InfinityDiagram
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The raw infinity ideal on a scalar word fibre

The original Cartesian projection and section determine the scalar infinity
section. Its ideal is preserved by the specified raw Cartier map on every
open, and by the specified splitting obtained by section insertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

open private unitModule chartRaw polynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private nodePrior from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
open private infinity_coeff infinity_base from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.InfinityDiagram
open private projective_pullback from
  OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
open private node_base_equation from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarInfinitySplitting

namespace SchubertGeometry.ProjectiveCartier

private theorem iso_app_eq_zero
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (f' : Z' ⟶ X) (f : Z ⟶ X)
    (he : e.hom ≫ f' = f) (V : X.Opens) (a : Γ(X, V)) :
    f.app V a = 0 ↔ f'.app V a = 0 := by
  subst f
  simp only [Scheme.Hom.comp_app]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1

private theorem pullback_app_eq_zero
    {X Y D Z Z' : Scheme.{u}} {q : X ⟶ Y} {d : D ⟶ Y}
    {f : Z ⟶ X} {z : Z ⟶ D} {f' : Z' ⟶ X} {z' : Z' ⟶ D}
    (h : IsPullback f z q d) (h' : IsPullback f' z' q d)
    (V : X.Opens) (a : Γ(X, V)) :
    f.app V a = 0 ↔ f'.app V a = 0 := by
  exact iso_app_eq_zero (h.isoIsPullback _ _ h') f' f
    (IsPullback.isoIsPullback_hom_fst X D h h') V a

/-- An affine morphism has affine ring coordinates on a prescribed affine pullback chart. -/
theorem exists_boundary_affine_chart
    {A : Type u} [CommRing A] {X Z : Scheme.{u}}
    (j : Spec (.of A) ⟶ X) (d : Z ⟶ X) [IsAffineHom d] :
    ∃ (B : CommRingCat.{u}) (g : A →+* B) (b : Spec B ⟶ Z),
      IsPullback (Spec.map (CommRingCat.ofHom g)) b j d := by
  let P := pullback j d
  let : IsAffine P := isAffine_of_isAffineHom (pullback.fst j d)
  let e : Spec (.of Γ(P, ⊤)) ≅ P := P.isoSpec.symm
  refine ⟨.of Γ(P, ⊤), (Spec.preimage (e.hom ≫ pullback.fst j d)).hom,
    e.hom ≫ pullback.snd j d, ?_⟩
  change IsPullback (Spec.map (Spec.preimage (e.hom ≫ pullback.fst j d))) _ j d
  rw [Spec.map_preimage]
  apply (IsPullback.of_hasPullback j d).of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  all_goals simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Raw preservation transports between two Cartesian presentations of a boundary. -/
theorem raw_preserves_of_pullbacks
    {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X Y D Z Z' : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    {q : X ⟶ Y} {d : D ⟶ Y}
    {f : Z ⟶ X} {z : Z ⟶ D} {f' : Z' ⟶ X} {z' : Z' ⟶ D}
    (h : IsPullback f z q d) (h' : IsPullback f' z' q d)
    (hraw : ∀ (V : X.Opens) (a : Γ(X, V)), f'.app V a = 0 →
      ∀ e : Γ(L, V), f'.app V (Θ.app V (a • e)) = 0) :
    ∀ (V : X.Opens) (a : Γ(X, V)), f.app V a = 0 →
      ∀ e : Γ(L, V), f.app V (Θ.app V (a • e)) = 0 := by
  intro V a ha e
  exact (pullback_app_eq_zero h h' V _).mpr
    (hraw V a ((pullback_app_eq_zero h h' V a).mp ha) e)


private theorem raw_inserted_compatible
    {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X Z : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (f : Z ⟶ X) [QuasiCompact f] (m : unitModule X ⟶ L)
    (S : SchemeSplitting X p)
    (hS : S.toOperator = twistedSectionOperator base L Θ (m.app ⊤ (1 : Γ(X, ⊤))))
    (hraw : ∀ (V : X.Opens) (a : Γ(X, V)), f.app V a = 0 →
      ∀ e : Γ(L, V), f.app V (Θ.app V (a • e)) = 0) :
    S.IsCompatible f.ker := by
  intro V a ha
  rw [Scheme.Hom.ker_apply] at ha ⊢
  have h := congrArg (fun φ : SchemeFrobeniusMap X p => φ.onOpen V a) hS
  change S.onOpen V a = Θ.app V
    (a • L.presheaf.map (homOfLE (le_top : (V : X.Opens) ≤ ⊤)).op
      (m.app ⊤ (1 : Γ(X, ⊤)))) at h
  exact (congrArg (f.app V) h).trans (hraw V a ha _)

end SchubertGeometry.ProjectiveCartier

namespace SchubertGeometry.RetainedCharacter

private theorem cocone_cover {Idx : Type u} [Category Idx] [Quiver.IsThin Idx]
    (F : Idx ⥤ Scheme.{u})
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion (F.map f)]
    [(F ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone F) (hc : IsColimit c) (z : c.pt) :
    ∃ i y, c.ι.app i y = z := by
  let e : colimit F ≅ c.pt := (colimit.isColimit F).coconePointUniqueUpToIso hc
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F (e.inv z)
  refine ⟨i, y, ?_⟩
  have hi := (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  have hiy : e.hom (colimit.ι F i y) = c.ι.app i y :=
    congrArg (fun f : F.obj i ⟶ c.pt => f y) hi
  have he : e.hom (e.inv z) = z :=
    congrArg (fun f : c.pt ⟶ c.pt => f z) e.inv_hom_id
  exact hiy.symm.trans ((congrArg e.hom hy).trans he)

variable {C R J : Type u} [Field C] [CommRing R] [Algebra C R]
    {p : ℕ} [ExpChar C p] [PerfectRing C p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (basePrior : cN.pt.left ⟶ Spec (.of C))
    (Θ : frobeniusRestriction C p basePrior
      (matchingModule N cN delta ((p - 1) / 2)) ⟶ unitModule cN.pt.left)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})

/-- The scalar infinity section has its ideal preserved on every open
by the specified raw word Cartier map. The same section and the same chosen
splitting also satisfy normalized compatibility. -/
theorem scalarWord_raw_boundary
    {B₀ X₀ S₀ X : Scheme.{u}} (base₀ : B₀ ⟶ S₀) (baseX₀ : X₀ ⟶ S₀)
    (π₀ : X₀ ⟶ B₀) (δ₀ : B₀ ⟶ X₀) [IsClosedImmersion δ₀]
    (hδ₀ : δ₀ ≫ π₀ = 𝟙 B₀) (hbase₀ : π₀ ≫ base₀ = baseX₀)
    (b : cN.pt.left ⟶ B₀) (x : X ⟶ X₀) (baseX : X ⟶ Spec (.of R))
    (t : Spec (.of R) ⟶ S₀) (hb : IsPullback b cN.pt.hom base₀ t)
    (hx : IsPullback x baseX baseX₀ t)
    (A₀ : {s : Finset J // s.Nonempty} → Type u) [∀ s, CommRing (A₀ s)]
    (f : ∀ s, A₀ s →+* N.obj s)
    (a₀ : ∀ s, Spec (.of (A₀ s)) ⟶ B₀) (k₀ : ∀ s, line (A₀ s) ⟶ X₀)
    (hk₀ : ∀ s, k₀ s ≫ π₀ =
      projectiveToSpec (A₀ s) (ULift.{u} (Fin 2)) ≫ a₀ s)
    (hs₀ : ∀ s, projectiveLineSection (A₀ s) ⟨1⟩ ≫ k₀ s = a₀ s ≫ δ₀)
    (Knode : ∀ s, line (N.obj s) ⟶ X) [∀ s, IsOpenImmersion (Knode s)]
    (hKold : ∀ s, Knode s ≫ x =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (f s) ≫ k₀ s)
    (hKbase : ∀ s, Knode s ≫ baseX =
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))))
    (ha : ∀ s, (cN.ι.app (op s)).left ≫ b =
      Spec.map (CommRingCat.ofHom (f s)) ≫ a₀ s)
    (L : X.Modules) (m : unitModule X ⟶ L)
    (E : ∀ s j, (Scheme.Modules.pullback (polynomialLeg N Knode s j)).obj L ≅
      unitModule (Spec (.of (Polynomial (N.obj s)))))
    (ΘX : frobeniusRestriction C p
      (baseX ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) L ⟶ unitModule X)
    (S : SchemeSplitting X p)
    (hS : S.toOperator = ProjectiveCartier.twistedSectionOperator
      (baseX ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) L ΘX
        (m.app ⊤ (1 : Γ(X, ⊤))))
    (hraw : ∀ s j, ΘX.over (polynomialLeg N Knode s j).opensRange =
      chartRaw N cN hcN delta hco hn basePrior Θ sel Knode
        (baseX ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) L E s j) :
    ∃ (π : X ⟶ cN.pt.left) (δ : cN.pt.left ⟶ X),
      δ ≫ π = 𝟙 _ ∧ IsClosedImmersion δ ∧
      π ≫ b = x ≫ π₀ ∧ π ≫ cN.pt.hom = baseX ∧
      δ ≫ x = b ≫ δ₀ ∧ δ ≫ baseX = cN.pt.hom ∧
      IsPullback x π π₀ b ∧ IsPullback b δ δ₀ x ∧
      (∀ s, projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
        (cN.ι.app (op s)).left = Knode s ≫ π) ∧
      (∀ s, projectiveLineSection (N.obj s) ⟨1⟩ ≫ Knode s =
        (cN.ι.app (op s)).left ≫ δ) ∧
      S.IsCompatible δ.ker ∧
      ∀ (V : X.Opens) (a : Γ(X, V)), δ.app V a = 0 →
        ∀ e : Γ(L, V), δ.app V (ΘX.app V (a • e)) = 0 := by
  classical
  obtain ⟨π, δ, hδ, hclosed, hπb, hπbase, hδx, hδbase, hpull, hspull⟩ :=
    exists_scalar_section base₀ baseX₀ π₀ δ₀ hδ₀ hbase₀ b x cN.pt.hom baseX t hb hx
  let : IsClosedImmersion δ := hclosed
  have hprior := retained_prior_charts N cN hcN
  have hnodes (s : {s : Finset J // s.Nonempty}) :
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫ (cN.ι.app (op s)).left =
          Knode s ≫ π ∧
        projectiveLineSection (N.obj s) ⟨1⟩ ≫ Knode s =
          (cN.ι.app (op s)).left ≫ δ :=
    scalar_section_node base₀ baseX₀ π₀ δ₀ b x cN.pt.hom baseX t hb hx
      π δ hπb hπbase hδx hδbase
      (projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)))
      (projectiveLineSection (N.obj s) ⟨1⟩)
      (projectiveToSpec (A₀ s) (ULift.{u} (Fin 2)))
      (projectiveLineSection (A₀ s) ⟨1⟩)
      (projectiveCoeffMap (ULift.{u} (Fin 2)) (f s))
      (Spec.map (CommRingCat.ofHom (f s))) (Knode s) (k₀ s)
      (cN.ι.app (op s)).left (a₀ s) infinity_base
      (projective_pullback (ι := ULift.{u} (Fin 2)) (f s)).w
      (infinity_coeff (f s)) (hk₀ s) (hs₀ s) (hKold s)
      (node_base_equation _ _ _ _ _ _ (hprior.2.2 s) (hKbase s)) (ha s)
  let F := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let c := (Over.forget (Spec (.of R))).mapCocone cN
  have hc : IsColimit c := isColimitOfPreserves (Over.forget (Spec (.of R))) hcN
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (F.map f) := fun {s t} f => by
    change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom))
    infer_instance
  have hcover : ∀ z : cN.pt.left, ∃ s y, (cN.ι.app (op s)).left y = z := by
    intro z
    obtain ⟨s, y, hy⟩ := cocone_cover F c hc z
    exact ⟨s.unop, y, hy⟩
  let : ∀ s, Algebra C (N.obj s) := fun s =>
    ((algebraMap R (N.obj s)).comp (algebraMap C R)).toAlgebra
  let ψ : ∀ s, FrobeniusLinearMap (N.obj s) p := fun s =>
    nodePrior N cN hcN delta hco hn basePrior Θ s (sel s).1 (sel s).2
  have hΘ (s) : ΘX.over (projectiveLinePolynomialChart (N.obj s) ⟨1⟩ ≫ Knode s).opensRange =
      ProjectiveCartier.relativeCartierWordChart (ψ s) ⟨1⟩
        (baseX ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) L
        (projectiveLinePolynomialChart (N.obj s) ⟨1⟩ ≫ Knode s) (E s ⟨1⟩) := hraw s ⟨1⟩
  have hrawδ := @ProjectiveCartier.wordCartier_raw_infinity
    C _ p _ _ X cN.pt.left
    (baseX ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) L ΘX π δ inferInstance hδ
    {s : Finset J // s.Nonempty} (fun s => N.obj s)
    (fun s => inferInstance) (fun s => inferInstance)
    (fun s => (cN.ι.app (op s)).left) hprior.1 Knode (fun s => inferInstance)
    (fun s => (hnodes s).1.symm) (fun s => (hnodes s).2) hcover
    (fun s => E s ⟨1⟩) ψ hΘ
  have hcompatible := ProjectiveCartier.raw_inserted_compatible
    (baseX ≫ Spec.map (CommRingCat.ofHom (algebraMap C R))) L ΘX δ m S hS hrawδ
  exact ⟨π, δ, hδ, hclosed, hπb, hπbase, hδx, hδbase, hpull, hspull,
    (fun s => (hnodes s).1), (fun s => (hnodes s).2), hcompatible, hrawδ⟩

end SchubertGeometry.RetainedCharacter
