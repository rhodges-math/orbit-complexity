import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
import OrbitComplexity.SchubertGeometry.Normality.Transitions.ProperEndpointCharts
import OrbitComplexity.SchubertGeometry.Normality.Transitions.TransitionFamilies
import OrbitComplexity.SchubertGeometry.BSDH.EndpointCharts
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PreimageCoordinateCocone
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Word character models from finite endpoint covers

Endpoint charts descend to a finite affine refinement after a common coefficient
extension. Their coordinate restrictions supply the Borel transitions and the
retained word character line on that same scalar extension of the proper model.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct CategoryTheory.MonObj
open CartesianMonoidalCategory MonoidalCategory

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

open private inverseOpenDiagram_eq inverseCoordinates_affine fieldCoordinateMap
  fieldCoordinateCocone fieldCoordinateCocone_colimit fieldCoordinateCocone_leg
  fieldCoordinateDiagram_opens retainedStageResult
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private inverseOpenDiagram fieldSchemeDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private section_character_laws
  from OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter
open private map_stage
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent

private theorem endpoint_comp {C : Type*} [Category C] {A B D E F : C}
    (p : A ⟶ B) (a : B ⟶ D) (g : D ⟶ F) (b : B ⟶ E)
    (f : E ⟶ F) (c : A ⟶ E)
    (ha : a ≫ g = b ≫ f) (hp : p ≫ b = c) :
    (p ≫ a) ≫ g = c ≫ f :=
  (Category.assoc p a g).trans
    ((congrArg (fun z => p ≫ z) ha).trans
      ((Category.assoc p b f).symm.trans (congrArg (fun z => z ≫ f) hp)))

private theorem restricted_comp {C : Type*} [Category C] {A B D E F : C}
    (f : A ⟶ B) (pb : B ⟶ D) (pa : A ⟶ D)
    (a : D ⟶ E) (g : E ⟶ F) (hp : f ≫ pb = pa) :
    (f ≫ (pb ≫ a)) ≫ g = (pa ≫ a) ≫ g :=
  congrArg (fun z => z ≫ g)
    ((Category.assoc f pb a).symm.trans (congrArg (fun z => z ≫ a) hp))

private theorem factor_transport {A : Type*} [Mul A]
    (xj xk yj yk b : A) (hj : xj = yj) (hk : xk = yk)
    (h : yj = yk * b) : xj = xk * b :=
  hj.trans (h.trans (congrArg (fun z => z * b) hk.symm))

private theorem coordinate_frame_eq {K : Type u} [CommRing K]
    {I : Type u} [Category I] (E : I ⥤ Over (Spec (.of K)))
    (h₁ h₂ : ∀ s, IsAffine (E.obj s).left) (s : I) :
    (by letI := h₁; exact ((coordinateDiagramIso (.of K) E).inv.app s).left) =
      (by letI := h₂; exact ((coordinateDiagramIso (.of K) E).inv.app s).left) := rfl

private theorem bind_open_data
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {P₁ P₂ P₃ : ∀ a, B a → Prop}
    {Q₁ Q₂ Q₃ : ∀ a b, C a b → Prop} {Z : Prop}
    (h : ∃ a b, P₁ a b ∧ P₂ a b ∧ P₃ a b ∧
      ∃ c, Q₁ a b c ∧ Q₂ a b c ∧ Q₃ a b c)
    (f : ∀ a b, P₃ a b → ∀ c, Q₁ a b c → Q₂ a b c → Q₃ a b c → Z) : Z := by
  obtain ⟨a, b, _, _, hp, c, hq₁, hq₂, hq₃⟩ := h
  exact f a b hp c hq₁ hq₂ hq₃

private theorem bind_transition_data {B : Sort*} {G H N C P : B → Prop} {Z : Prop}
    (h : ∃ b, G b ∧ H b ∧ N b ∧ C b ∧ P b)
    (f : ∀ b, G b → N b → C b → Z) : Z := by
  obtain ⟨b, hg, _, hn, hc, _⟩ := h
  exact f b hg hn hc

private theorem pack_geometry
    {I A : Sort*} {H : I → A → Prop} {B : ∀ i a, H i a → Sort*}
    {G N C : ∀ i a h, B i a h → Prop}
    {Q : ∀ i a h b, G i a h b → N i a h b → C i a h b → Prop}
    (i : I) (a : A) (h : H i a) (b : B i a h)
    (hg : G i a h b) (hn : N i a h b) (hc : C i a h b)
    (hq : Q i a h b hg hn hc) :
    ∃ i a h b hg hn hc, Q i a h b hg hn hc :=
  ⟨i, a, h, b, hg, hn, hc, hq⟩

private theorem bind_four_exists
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {P : ∀ a b c, D a b c → Prop} {Q : Prop}
    (h : ∃ a b c d, P a b c d)
    (f : ∀ a b c d, P a b c d → Q) : Q := by
  obtain ⟨a, b, c, d, hp⟩ := h
  exact f a b c d hp

private theorem bind_exists {A : Sort*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (f : ∀ a, P a → Q) : Q := by
  obtain ⟨a, hp⟩ := h
  exact f a hp

private theorem choose_family {J : Sort*} {A : J → Sort*}
    {P : ∀ j, A j → Prop} (h : ∀ j, ∃ a, P j a) :
    ∃ a : ∀ j, A j, ∀ j, P j (a j) :=
  ⟨fun j => (h j).choose, fun j => (h j).choose_spec⟩

private theorem bind_endpoint_cover
    {V : Sort*} {Fin Aff : V → Prop} {I : V → Sort*} {A : ∀ v, I v → Sort*}
    {H P : ∀ v i, A v i → Prop} {Q : Prop}
    (h : ∃ v, Fin v ∧ Aff v ∧ ∃ i a, H v i a ∧ P v i a)
    (f : ∀ v, Fin v → Aff v → ∀ i a, H v i a → P v i a → Q) : Q := by
  obtain ⟨v, hfin, haff, i, a, hh, hp⟩ := h
  exact f v hfin haff i a hh hp

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

private def coordinateChart (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (V : J → Over (Spec (.of K)))
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V j)
    (a : ∀ j, V j ⟶ (oppositeUnipotentVariety G).toOver) (j : J) :
    (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver :=
  p (singletonIndex j) j (Finset.mem_singleton_self j) ≫ a j

private theorem coordinate_chart_lift (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (V : J → Over (Spec (.of K)))
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V j)
    (hp : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (point : J → G.points) (a : ∀ j, V j ⟶ (oppositeUnipotentVariety G).toOver)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    chartLift G F point (coordinateChart G F V p a) s j hj =
      (p s j hj ≫ a j) ≫ flagChartMap G (point j) :=
  restricted_comp
    ((algSpec (.of K)).map (F.map (singletonArrow s j hj)).op)
    (p (singletonIndex j) j (Finset.mem_singleton_self j)) (p s j hj)
    (a j) (flagChartMap G (point j))
    (hp (singletonIndex j) s (singletonArrow s j hj) j (Finset.mem_singleton_self j))

private theorem cover_preimage {X Y : Scheme.{u}} (q : X ⟶ Y)
    (W : Y.OpenCover.{u}) :
    (⨆ j, q ⁻¹ᵁ (W.f j).opensRange) = ⊤ :=
  (TopologicalSpace.Opens.map_iSup q.base (fun j => (W.f j).opensRange)).symm.trans
    ((congrArg (fun V : Y.Opens => q ⁻¹ᵁ V) W.iSup_opensRange).trans
      (TopologicalSpace.Opens.map_top q.base))

omit [IsAlgClosed K] [CharZero K] in
private theorem affine_preimage {S : Type u} [CommRing S] [Algebra S K]
    {Y X : Scheme.{u}} (base : Y ⟶ Spec (.of S)) (baseK : X ⟶ Spec (.of K))
    (q : X ⟶ Y)
    (h : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.Opens) (hU : IsAffineOpen U) : IsAffineOpen (q ⁻¹ᵁ U) := by
  let : IsAffine U.toScheme := hU
  exact IsAffine.of_isPullback ((isPullback_morphismRestrict q U).paste_vert h)

/-- Finite endpoint charts on one proper scalar model supply the full retained
word character, all coefficient equations, and every determinant power. -/
def wordCoverModels
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    [(bsdhScheme G word).IsSeparated]
    (qK : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) (hW : ∀ j, IsAffine (W.X j)) : Prop :=
  let U := fun j => (W.f j).opensRange
  let hU : ∀ j, IsAffineOpen (U j) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let M := intersectionCoordinates base (intersectionOpens U)
  let F := intersectionCoordinates (bsdhToSpec G word)
    (inverseOpenDiagram qK (intersectionOpens U))
  let hEK := inverseCoordinates_affine base (bsdhToSpec G word) qK hK U hU
  let cF := fieldCoordinateCocone (bsdhToSpec G word) qK U hEK
  let hcF := fieldCoordinateCocone_colimit (bsdhToSpec G word) qK U
    W.iSup_opensRange hEK
  let q : cF.pt.left ⟶ bsdhScheme G word := 𝟙 _
  let hF := fieldCoordinateDiagram_opens base (bsdhToSpec G word) qK hK U hU
  letI : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    fun {_ _} f => hF.1 _ _ f
  letI : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
    Scheme.forget).IsLocallyDirected := hF.2
  ∃ (point : W.I₀ → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset W.I₀ // s.Nonempty}) (j : W.I₀) (_ : j ∈ s.val)
      (k : W.I₀) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
    let laws := section_character_laws G F beta hnatural hbeta
    ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
      (∀ s k x, e s (k ⊗ₜ[S] x) =
        algebraMap K (F.obj s) k * fieldCoordinateMap base (bsdhToSpec G word) qK U s x) ∧
      (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom) ∧
      ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
        retainedStageResult G S base (bsdhToSpec G word) qK U cF hcF rfl word q
          point a ha beta hgroup laws.1 laws.2 i e T hST R hTR

private def coordinateCoverResult
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {Y X : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [X.IsSeparated]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) (hW : ∀ j, IsAffine (W.X j))
    (q : X ⟶ bsdhScheme G word) : Prop :=
  let U := fun j => (W.f j).opensRange
  let hU : ∀ j, IsAffineOpen (U j) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let M := intersectionCoordinates base (intersectionOpens U)
  let F := intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))
  let hEK := inverseCoordinates_affine base (baseK) qK hK U hU
  let cF := fieldCoordinateCocone (baseK) qK U hEK
  let hcF := fieldCoordinateCocone_colimit (baseK) qK U
    W.iSup_opensRange hEK
  let hF := fieldCoordinateDiagram_opens base (baseK) qK hK U hU
  letI : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    fun {_ _} f => hF.1 _ _ f
  letI : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
    Scheme.forget).IsLocallyDirected := hF.2
  ∃ (point : W.I₀ → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset W.I₀ // s.Nonempty}) (j : W.I₀) (_ : j ∈ s.val)
      (k : W.I₀) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
    let laws := section_character_laws G F beta hnatural hbeta
    ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
      (∀ s k x, e s (k ⊗ₜ[S] x) =
        algebraMap K (F.obj s) k * fieldCoordinateMap base (baseK) qK U s x) ∧
      (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom) ∧
      ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
        retainedStageResult G S base (baseK) qK U cF hcF rfl word q
          point a ha beta hgroup laws.1 laws.2 i e T hST R hTR

private theorem pack_word_models
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y X : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base] [X.IsSeparated]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) [Finite W.I₀] (hW : ∀ j, IsAffine (W.X j))
    (q : X ⟶ bsdhScheme G word) :
  let U := fun j => (W.f j).opensRange
  let hU : ∀ j, IsAffineOpen (U j) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let _M := intersectionCoordinates base (intersectionOpens U)
  let F := intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))
  let hEK := inverseCoordinates_affine base (baseK) qK hK U hU
  let cF := fieldCoordinateCocone (baseK) qK U hEK
  let _hcF := fieldCoordinateCocone_colimit (baseK) qK U
    W.iSup_opensRange hEK
  ∀ (point : W.I₀ → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (_ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset W.I₀ // s.Nonempty}) (j : W.I₀) (_ : j ∈ s.val)
      (k : W.I₀) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (_hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (_hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (_hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
    coordinateCoverResult G word i S base baseK qK hK W hW q := by
  intro U hU M F hEK cF hcF point a ha beta hgroup hnatural hbeta
  let hF := fieldCoordinateDiagram_opens base baseK qK hK U hU
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    fun {_ _} f => hF.1 _ _ f
  let : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected := hF.2
  exact pack_geometry
            (Q := fun point a ha beta hgroup hnatural hbeta =>
              let laws := section_character_laws G F beta hnatural hbeta
              ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
                (∀ s k x, e s (k ⊗ₜ[S] x) = algebraMap K (F.obj s) k *
                  fieldCoordinateMap base (baseK) qK U s x) ∧
                (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
                    (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
                  (F.map f).hom.comp (e s).toAlgHom) ∧
                ∃ (T : Subalgebra ℤ K) (hST : S ≤ T)
                  (R : Subalgebra ℤ K) (hTR : T ≤ R),
                  retainedStageResult G S base (baseK) qK U cF hcF rfl
                    word q point a ha beta hgroup laws.1 laws.2 i e T hST R hTR)
            point a ha beta hgroup hnatural hbeta
            (exists_retained_word_model
              (K := K) (G := G) (S := S) (hS := hS)
              (base := base) (baseK := baseK) (qK := qK) (hK := hK)
              (U := U) (hU := hU) (hcover := W.iSup_opensRange)
              (word := word) (i := i) (q := q) (point := point) (a := a) (ha := ha)
              (beta := beta) (hgroup := hgroup) (hnatural := hnatural) (hbeta := hbeta))

private theorem compose_common {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : A ⟶ D) (j : B ⟶ E) (k : D ⟶ E) (q : E ⟶ F)
    (h : a ≫ j = b ≫ k) : a ≫ (j ≫ q) = b ≫ (k ≫ q) :=
  (Category.assoc a j q).symm.trans
    ((congrArg (fun z => z ≫ q) h).trans (Category.assoc b k q))

private theorem identity_endpoint {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (f : B ⟶ E) (j : A ⟶ D) (g : D ⟶ E)
    (h : a ≫ f = j ≫ g) : a ≫ f = j ≫ (𝟙 D ≫ g) :=
  h.trans (congrArg (fun z => j ≫ z) (Category.id_comp g).symm)

private theorem identity_cartesian {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : A ⟶ D) (j : B ⟶ E) (g : D ⟶ E)
    (h : IsPullback a b j g) : IsPullback a b (j ≫ 𝟙 E) g := by
  simpa only [Category.comp_id] using h

private theorem coordinate_word_geometry_model
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y X : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    [X.IsSeparated]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) [Finite W.I₀] (hW : ∀ j, IsAffine (W.X j))
    (q : Over.mk baseK ⟶ Over.mk (bsdhToSpec G word)) :
    let U := fun j => (W.f j).opensRange
    let O := fun j => qK ⁻¹ᵁ U j
    let hcover := cover_preimage qK W
    let VK := X.openCoverOfIsOpenCover O hcover
    ∀ (point : W.I₀ → G.points)
      (a : ∀ j, Over.mk (VK.f j ≫ baseK) ⟶
        (oppositeUnipotentVariety G).toOver)
      (c : ∀ j, Over.mk (VK.f j ≫ baseK) ⊗
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
          Over.mk (bsdhToSpec G (word ++ [i])))
      (_ha : ∀ j, (a j).left ≫ flagSchemeChart G (point j) =
        VK.f j ≫ (q.left ≫ bsdhMap G word))
      (_hc : ∀ j, IsPullback
        (fst (Over.mk (VK.f j ≫ baseK))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
        (c j).left (VK.f j ≫ q.left) (bsdhAppendFst G word i))
      (_he : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
        (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (point j)),
      coordinateCoverResult G word i S base baseK qK hK W hW q.left := by
  intro U O hcover VK point a c ha hc he
  unfold coordinateCoverResult
  intro U₀ hU M F hEK cF hcF hF
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    fun {_ _} f => hF.1 _ _ f
  let : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected := hF.2
  let V := inverseOpenDiagram qK (intersectionOpens U₀)
  let E := fieldSchemeDiagram baseK V
  have hO : ∀ j, IsAffineOpen (O j) :=
    fun j => affine_preimage base baseK qK hK (U₀ j) (hU j)
  have hV : V = intersectionOpens O := inverseOpenDiagram_eq qK U₀
  exact bind_open_data
    (open_diagram_coordinate_cocone baseK O hO hcover V hV)
    (fun hE b hbleg p hp hpn hcommon => by
      have hblegF (s : {s : Finset W.I₀ // s.Nonempty}ᵒᵖ) :
          b.app s = (cF.ι.app s).left :=
        (hbleg s).trans
          ((congrArg
            (fun z : ((algSpec (.of K)).obj (op (F.obj s.unop))).left ⟶
                (E.obj s).left => z ≫ (V.obj s).ι)
            (coordinate_frame_eq E hE hEK s)).trans
              (fieldCoordinateCocone_leg baseK qK U₀ hEK s).symm)
      let aF := coordinateChart G F (fun j => Over.mk (VK.f j ≫ baseK)) p a
      have haF (j : W.I₀) :
          (aF j).left ≫ (flagChartMorphism G (point j)).left =
            (cF.ι.app (op (singletonIndex j))).left ≫ (q.left ≫ bsdhMap G word) :=
        (endpoint_comp
          (p (singletonIndex j) j (Finset.mem_singleton_self j)).left (a j).left
          (flagSchemeChart G (point j)) (VK.f j) (q.left ≫ bsdhMap G word)
          (cF.ι.app (op (singletonIndex j))).left (ha j)
          ((hp (singletonIndex j) j (Finset.mem_singleton_self j)).trans
            (hblegF (op (singletonIndex j)))))
      exact bind_transition_data
        (bsdh_transition_family G word i F
          (fun j => Over.mk (VK.f j ≫ baseK))
          (fun j => Over.homMk (V := Over.mk baseK) (VK.f j) rfl ≫ q)
          p hpn
          (fun s j hj k hk => compose_common _ _ _ _ q (hcommon s j hj k hk))
          point a (fun j => (ha j).trans (Category.assoc _ _ _).symm)
          c (fun j => (hc j).w) he)
        (fun beta hgroup hnatural hbeta => by
          have hgroupF (s : {s : Finset W.I₀ // s.Nonempty})
              (j : W.I₀) (hj : j ∈ s.val) (k : W.I₀) (hk : k ∈ s.val) :
              chartLift G F point aF s j hj =
                chartLift G F point aF s k hk * (beta s j hj k hk ≫ borelInclusion G) :=
            factor_transport _ _ _ _ _
              (coordinate_chart_lift G F
                (fun j => Over.mk (VK.f j ≫ baseK)) p hpn point a s j hj)
              (coordinate_chart_lift G F
                (fun j => Over.mk (VK.f j ≫ baseK)) p hpn point a s k hk)
              (hgroup s j hj k hk)
          exact pack_word_models
            (K := K) (G := G) (word := word) (i := i) (S := S) (hS := hS)
            (X := X) (Y := Y) (base := base)
            (baseK := baseK) (qK := qK) (hK := hK)
            (W := W) (hW := hW) (q := q.left)
            point aF haF beta hgroupF hnatural hbeta))

private theorem coordinate_word_models
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    [(bsdhScheme G word).IsSeparated]
    (qK : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) [Finite W.I₀] (hW : ∀ j, IsAffine (W.X j)) :
    let U := fun j => (W.f j).opensRange
    let O := fun j => qK ⁻¹ᵁ U j
    let hcover := cover_preimage qK W
    let VK := (bsdhScheme G word).openCoverOfIsOpenCover O hcover
    ∀ (point : W.I₀ → G.points)
      (a : ∀ j, Over.mk (VK.f j ≫ bsdhToSpec G word) ⟶
        (oppositeUnipotentVariety G).toOver)
      (c : ∀ j, Over.mk (VK.f j ≫ bsdhToSpec G word) ⊗
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
          Over.mk (bsdhToSpec G (word ++ [i])))
      (_ha : ∀ j, (a j).left ≫ flagSchemeChart G (point j) =
        VK.f j ≫ bsdhMap G word)
      (_hc : ∀ j, IsPullback
        (fst (Over.mk (VK.f j ≫ bsdhToSpec G word))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
        (c j).left (VK.f j) (bsdhAppendFst G word i))
      (_he : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
        (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (point j)),
      wordCoverModels G word i S base qK hK W hW := by
  intro U O hcover VK point a c ha hc he
  exact coordinate_word_geometry_model
    (K := K) (G := G) (word := word) (i := i) (S := S) (hS := hS)
    (Y := Y) (X := bsdhScheme G word) (base := base)
    (baseK := bsdhToSpec G word) (qK := qK) (hK := hK)
    (W := W) (hW := hW) (q := 𝟙 (Over.mk (bsdhToSpec G word)))
    point a c
    (fun j => identity_endpoint _ _ _ _ (ha j))
    (fun j => identity_cartesian _ _ _ _ (hc j)) he

section Refinement

variable
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S))
    (qY : bsdhScheme G word ⟶ Y)
    [(bsdhScheme G word).IsSeparated]

/-- A finite coefficient extension and affine cover preserve both projections
of the original scalar square and carry the retained word line and section. -/
def wordCoverStage (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
    (qT : YT ⟶ Y) (mT : bsdhScheme G word ⟶ YT)
    (hproper : IsProper baseT) (_hsmooth : Smooth baseT)
    (_hTcart : IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hKcart : IsPullback mT (bsdhToSpec G word) baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K)))),
    mT ≫ qT = qY ∧
    ∃ (W : YT.OpenCover.{u}) (_hfinite : Finite W.I₀) (haff : ∀ j, IsAffine (W.X j)),
      letI : IsProper baseT := hproper
      wordCoverModels G word i T baseT mT hKcart W haff

variable
    (V : (bsdhScheme G word).OpenCover.{u}) (point : V.I₀ → G.points)
    (a : ∀ j, Over.mk (V.f j ≫ bsdhToSpec G word) ⟶
      (oppositeUnipotentVariety G).toOver)
    (c : ∀ j, Over.mk (V.f j ≫ bsdhToSpec G word) ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))

private def endpointStageData (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
    (qT : YT ⟶ Y) (mT : bsdhScheme G word ⟶ YT),
    IsProper baseT ∧ Smooth baseT ∧
    IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))) ∧
    IsPullback mT (bsdhToSpec G word) baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
    mT ≫ qT = qY ∧
    ∃ (W : YT.OpenCover.{u}) (_ : Finite W.I₀) (_ : ∀ l, IsAffine (W.X l))
      (endpoint : W.I₀ → V.I₀),
      let O : W.I₀ → (bsdhScheme G word).Opens :=
        fun l => mT ⁻¹ᵁ (W.f l).opensRange
      ∃ hcover : (⨆ l, O l) = ⊤,
        let VK := (bsdhScheme G word).openCoverOfIsOpenCover O hcover
        (∀ l, IsAffine (VK.X l)) ∧
        ∃ d : ∀ l, Over.mk (VK.f l ≫ bsdhToSpec G word) ⟶
            Over.mk (V.f (endpoint l) ≫ bsdhToSpec G word),
          (∀ l, (d l).left ≫ V.f (endpoint l) = VK.f l) ∧
          (∀ l, (d l ≫ a (endpoint l)).left ≫ flagSchemeChart G (point (endpoint l)) =
            VK.f l ≫ bsdhMap G word) ∧
          (∀ l, IsPullback
            (fst (Over.mk (VK.f l ≫ bsdhToSpec G word))
              (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
            ((d l ⊗ₘ 𝟙 _) ≫ c (endpoint l)).left (VK.f l) (bsdhAppendFst G word i)) ∧
          ∀ l, ((d l ⊗ₘ 𝟙 _) ≫ c (endpoint l)).left ≫
            (bsdhAppendIso G word i).hom.left ≫
              pullback.snd (bsdhMap G word) (flagBundleProjection G
                (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
            ((d l ≫ a (endpoint l)) ⊗ₘ 𝟙 _).left ≫
              flagBundleChart G _ (point (endpoint l))

private theorem complete_endpoint_stage (T : Subalgebra ℤ K) (hST : S ≤ T)
    (h : endpointStageData G word i S base qY V point a c T hST) :
    wordCoverStage G word i S base qY T hST := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  exact bind_four_exists (Q := wordCoverStage G word i S base qY T hST) h.2
    (fun YT baseT qT mT hm =>
      bind_four_exists (Q := wordCoverStage G word i S base qY T hST) hm.2.2.2.2.2
        (fun W hfinite haff endpoint hcoverData =>
          bind_exists (Q := wordCoverStage G word i S base qY T hST) hcoverData
            (fun hcover hchartData =>
              bind_exists (Q := wordCoverStage G word i S base qY T hST) hchartData.2
                (fun d hd => by
                  let : IsProper baseT := hm.1
                  let : Smooth baseT := hm.2.1
                  let : Finite W.I₀ := hfinite
                  have hmodels := coordinate_word_models G word i T h.1 baseT mT
                    hm.2.2.2.1 W haff
                    (fun j => point (endpoint j))
                    (fun j => d j ≫ a (endpoint j))
                    (fun j => (d j ⊗ₘ 𝟙 _) ≫ c (endpoint j))
                    hd.2.1 hd.2.2.1 hd.2.2.2
                  exact ⟨h.1, YT, baseT, qT, mT, hm.1, hm.2.1,
                    hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, W, hfinite, haff, hmodels⟩))))

end Refinement

private theorem wordSchemeSeparated (G : ReductiveGroupData K)
    (word : List G.rootBase.support) : (bsdhScheme G word).IsSeparated :=
  ⟨by
    rw [← terminal.comp_from (bsdhToSpec G word)]
    infer_instance⟩

private theorem exists_word_cover_stage
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (qY : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qY (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ j, IsAffine (U.X j)) :
    letI := wordSchemeSeparated G word
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      wordCoverStage G word i S base qY T hST := by
  let : (bsdhScheme G word).IsSeparated := wordSchemeSeparated G word
  change ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
    wordCoverStage G word i S base qY T hST
  exact bind_endpoint_cover
    (Q := ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      wordCoverStage G word i S base qY T hST)
    (bsdh_finite_endpoint_cover G word i)
    (fun V _ _ point a ha happend =>
      bind_exists
        (Q := ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
          wordCoverStage G word i S base qY T hST)
        (choose_family happend)
        (fun c hc =>
          map_stage
            (P := endpointStageData G word i S base qY V point a c)
            (Q := wordCoverStage G word i S base qY)
            (exists_proper_endpoint_charts
              (G := G) (word := word) (i := i) (S := S) (hS := hS)
              (base := base) (qY := qY) (h := hK) (U := U) (hU := hU)
              (V := V) (g := point) (a := a) (ha := ha) (c := c)
              (hcart := fun j => (hc j).1) (hend := fun j => (hc j).2.2))
            (fun T hST hstage =>
              complete_endpoint_stage
                (K := K) (G := G) (word := word) (i := i) (S := S)
                (base := base) (qY := qY) (V := V) (point := point) (a := a) (c := c)
                (T := T) (hST := hST) (h := hstage))))

/-- Every specified proper smooth word model admits a common coefficient
extension and finite affine cover carrying its word character and all
determinant powers. Both scalar squares retain the original field comparison. -/
theorem exists_word_cover_models
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (qY : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qY (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ j, IsAffine (U.X j)) :
    letI := wordSchemeSeparated G word
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      wordCoverStage G word i S base qY T hST :=
  exists_word_cover_stage
    (K := K) (G := G) (word := word) (i := i) (S := S) (hS := hS)
    (Y := Y) (base := base) (qY := qY) (hK := hK) (U := U) (hU := hU)

end SchubertGeometry.RetainedCharacter
