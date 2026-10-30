import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellRootCover
import OrbitComplexity.SchubertGeometry.Connectedness.CellGeometric
import OrbitComplexity.SchubertGeometry.Connectedness.LocalizedGraph
import OrbitComplexity.SchubertGeometry.Connectedness.CoverRoots
import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonInterval
import OrbitComplexity.BruhatIntervals.Graph.IntervalPaths

set_option autoImplicit false

/-! # Connected geometric fibres of arithmetic Richardson models

The finite graph of Bruhat covers selects reflection-root curves on one
coefficient stage. The retained cell cover and endpoint incidences give
connected geometric fibres after one principal localization of that stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FrobeniusSplitting
open ReductiveGroups BruhatIntervals GroupActions

namespace SchubertGeometry.CellContraction

universe u v

private theorem predicate_transport {T : Type*} (P : T → Prop)
    {x y : T} (h : x = y) (hx : P x) : P y := h ▸ hx

private theorem path_map {I J : Type*} {r : I → I → Prop} {s : J → J → Prop}
    (f : I → J) (hf : ∀ i j, r i j → s (f i) (f j))
    {i j : I} (h : Relation.ReflTransGen r i j) :
    Relation.ReflTransGen s (f i) (f j) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.tail (hf _ _ hstep)

private theorem paths_reindex {I J W : Type*} (rel : W → W → Prop)
    (label : I → W) (label' : J → W) (e : I ≃ J)
    (he : ∀ j, label (e.symm j) = label' j) (root : J)
    (hpath : ∀ j, Relation.ReflTransGen
      (fun p q => rel (label' p) (label' q)) root j) :
    ∀ i, Relation.ReflTransGen
      (fun p q => rel (label p) (label q)) (e.symm root) i := by
  intro i
  have hm : Relation.ReflTransGen
      (fun p q : I => rel (label p) (label q)) (e.symm root) (e.symm (e i)) :=
    path_map (s := fun p q : I => rel (label p) (label q)) e.symm (fun p q hpq => by
      rw [he p, he q]
      exact hpq) (hpath (e i))
  simpa only [Equiv.symm_apply_apply] using hm

private theorem with_root_choices {E W J : Type*} {P : E → W → J → Prop}
    {Q : Prop} (h : ∀ e, ∃ w i, P e w i)
    (next : ∀ (w : E → W) (i : E → J), (∀ e, P e (w e) (i e)) → Q) : Q := by
  classical
  choose w i hi using h
  exact next w i hi

private theorem use_cover {J : Type*} {H : J → Prop}
    {F S C : J → Type*} {P : ∀ j, F j → Prop}
    {Q : ∀ j, F j → S j → C j → Prop}
    {A : J → Type*} {NZ : ∀ j, A j → Prop}
    {Cover : ∀ j, F j → A j → Prop} {Goal : Prop}
    (h : ∃ (j : J) (_ : H j) (f : F j) (s : S j) (c : C j),
      P j f ∧ Q j f s c ∧ ∃ r : A j, NZ j r ∧ Cover j f r)
    (next : ∀ (j : J), H j → ∀ (f : F j) (s : S j) (c : C j),
      Q j f s c → ∀ r : A j, NZ j r → Cover j f r → Goal) : Goal := by
  obtain ⟨j, hj, f, s, c, _, hq, r, hr, hc⟩ := h
  exact next j hj f s c hq r hr hc

private theorem retain_result {J : Type*} {H : J → Prop} {A : J → Type*}
    {NZ P : ∀ j, A j → Prop} (j : J) (hj : H j) (r : A j)
    (hr : NZ j r) (hp : P j r) :
    ∃ (j : J) (_ : H j) (r : A j), NZ j r ∧ P j r :=
  ⟨j, hj, r, hr, hp⟩

private theorem unit_model_iso {S T : Scheme.{u}} (κ : T ⟶ S)
    (U : Over T) (hU : U = Over.mk (pullback.fst κ (𝟙 S))) : IsIso U.hom := by
  subst U
  change IsIso (pullback.fst κ (𝟙 S))
  infer_instance

private theorem graph_of_edge_data
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] (D : Over (Spec (.of R)))
    {I : Type v} (rel : I → I → Prop) (root : I)
    (X : I → Over (Spec (.of R))) (piece : ∀ i, X i ⟶ D)
    (origin : ∀ i, Spec (.of R) ⟶ (X i).left)
    (hSection : ∀ i, origin i ≫ (X i).hom = 𝟙 _)
    [∀ i, GeometricallyConnected (X i).hom]
    (U : Over (Spec (.of R))) [IsIso U.hom]
    (B : Over (Spec (.of R))) [GeometricallyConnected B.hom]
    (vertex : {z : I × I // rel z.1 z.2} × Bool → I)
    (s : ∀ _e : {z : I × I // rel z.1 z.2} × Bool, U ⟶ B)
    (c : ∀ _e : {z : I × I // rel z.1 z.2}, B ⟶ D)
    (anchor : ∀ _i : I, U ⟶ D)
    (hAnchor : ∀ i, anchor i = anchorArrow U (origin i) (hSection i) (piece i))
    (hSource : ∀ e, vertex (e, false) = e.val.1)
    (hTarget : ∀ e, vertex (e, true) = e.val.2)
    (hIncidence : ∀ e, s e ≫ c e.1 = anchor (vertex e))
    (hCover : ∀ y : D.left, D.hom y ∈ PrimeSpectrum.basicOpen r →
      ∃ i x, (piece i).left x = y)
    (hPath : ∀ i, Relation.ReflTransGen rel root i) :
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj D).hom := by
  exact SchubertGeometry.geomConnected_of_localized_graph r D rel root X piece origin
    hSection U (fun _ _ _ => B) (fun i j h => c ⟨(i, j), h⟩)
    (fun i j h => s (⟨(i, j), h⟩, false))
    (fun i j h => s (⟨(i, j), h⟩, true))
    (fun i j h => (hIncidence (⟨(i, j), h⟩, false)).trans
      ((congrArg anchor (hSource ⟨(i, j), h⟩)).trans (hAnchor i)))
    (fun i j h => (hIncidence (⟨(i, j), h⟩, true)).trans
      ((congrArg anchor (hTarget ⟨(i, j), h⟩)).trans (hAnchor j))) hCover hPath

private theorem reindex_cover {B W J : Type*}
    (P Q T : B → Prop) (root : W → J → B)
    (h : ∃ β, P β ∧ Q β ∧ T β)
    (hp : ∀ β, P β → ∃ w i, root w i = β) :
    ∃ w i, P (root w i) ∧ T (root w i) ∧ Q (root w i) := by
  obtain ⟨β, hP, hQ, hT⟩ := h
  obtain ⟨w, i, rfl⟩ := hp β hP
  exact ⟨w, i, hP, hT, hQ⟩

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (R : Subalgebra ℤ K)

private theorem cover_parameters (x y : G.weylGroup) :
    let : PartialOrder G.weylGroup := (weylCoxeterSystem G.rootBase).bruhatPartialOrder
    x ⋖ y → ∃ (w : G.weylGroup) (i : G.rootBase.support),
      G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) ∧
      G.rootBase.IsPos (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val)) ∧
      y = RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * x := by
  dsimp only
  intro h
  exact reindex_cover G.rootBase.IsPos
    (fun β => y = RootPairing.weylGroup.ofIdx G.rootSystem β * x)
    (fun β => G.rootBase.IsPos (G.rootSystem.weylGroupToPerm x⁻¹ β))
    (fun w (i : G.rootBase.support) => G.rootSystem.weylGroupToPerm w i.val)
    (SchubertGeometry.bruhatCover_root G x y h)
    (SchubertGeometry.rootCurve_simple_presentation G)

/-- Every chosen arithmetic Richardson target has connected geometric fibres
after extending its coefficient stage and localizing at one nonzero element. -/
theorem exists_cellArithmetic_connected (a b : G.weylGroup)
    (hab : WeylBruhatLE G.rootBase a b) (hR : R.FG)
    (M : ∀ t : cellPieceIndices G a b,
      ArithmeticContractionModel (R := R)
        (cellContractionAlg G a b t.val) (cellOriginAlg G a b t.val t.property))
    (D : Over (Spec (.of R))) [LocallyOfFinitePresentation D.hom] [QuasiCompact D.hom]
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (start : CoefficientStage R) :
    ∃ (k : CoefficientStage R) (_ : start ≤ k) (r : k.val), r ≠ 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra k.val A] [IsLocalization.Away r A],
        GeometricallyConnected
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k.val A)))).obj
            (stageScalarModel R D.hom k)).hom := by
  classical
  let cs := weylCoxeterSystem G.rootBase
  let : PartialOrder G.weylGroup := cs.bruhatPartialOrder
  let V := cellPieceIndices G a b
  let J := bruhatInterval cs a b
  let e : V ≃ J := cellPieceIntervalEquiv G a b
  let : Fintype J := (bruhatInterval_finite cs a b).fintype
  let : Fintype V := Fintype.ofEquiv J e.symm
  let rel : V → V → Prop := fun p q => p.val ⋖ q.val
  let E := {z : V × V // rel z.1 z.2}
  let : Fintype E := Fintype.ofFinite E
  have hab' : cs.BruhatLE a b := (SchubertGeometry.weyl_bruhat_iff G.rootBase a b).mp hab
  let rootJ : J := ⟨a, cs.bruhatLE_refl a, hab'⟩
  let root : V := e.symm rootJ
  have hPath : ∀ t : V, Relation.ReflTransGen rel root t :=
    paths_reindex (fun p q : G.weylGroup => p ⋖ q) Subtype.val Subtype.val e
      (fun _ => rfl) rootJ (bruhatInterval_cover_reachable cs a b hab')
  have hroots : ∀ z : E, ∃ (w : G.weylGroup) (i : G.rootBase.support),
      G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) ∧
      G.rootBase.IsPos (G.rootSystem.weylGroupToPerm z.val.1.val⁻¹
        (G.rootSystem.weylGroupToPerm w i.val)) ∧
      z.val.2.val = RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * z.val.1.val :=
    fun z => cover_parameters G z.val.1.val z.val.2.val z.property
  refine with_root_choices hroots ?_
  intro w i hp
  let x : E → G.weylGroup := fun z => z.val.1.val
  let y : E → G.weylGroup := fun z => RootPairing.weylGroup.ofIdx G.rootSystem
    (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z
  have hy : ∀ z : E, z.val.2.val = y z := fun z => (hp z).2.2
  have hax : ∀ z : E, WeylBruhatLE G.rootBase a (x z) :=
    fun z => (cellPieceIndex_bounds G a b z.val.1).1
  have hxy : ∀ z : E, WeylBruhatLE G.rootBase (x z) (y z) := fun z =>
    predicate_transport (WeylBruhatLE G.rootBase (x z)) (hy z)
      ((SchubertGeometry.weyl_bruhat_iff G.rootBase _ _).mpr z.property.le)
  have hyb : ∀ z : E, WeylBruhatLE G.rootBase (y z) b := fun z =>
    predicate_transport (fun t => WeylBruhatLE G.rootBase t b) (hy z)
      (cellPieceIndex_bounds G a b z.val.2).2
  have hne₁ : ∀ z : E, Nonempty (cellIntersection G a b (y z)).left := fun z =>
    predicate_transport (fun t => Nonempty (cellIntersection G a b t).left)
      (hy z) z.val.2.property
  let vertex : E × Bool → V := fun z =>
    if z.2 then ⟨y z.1, hne₁ z.1⟩ else z.1.val.1
  have hSource : ∀ z : E, vertex (z, false) = z.val.1 := fun _ => rfl
  have hTarget : ∀ z : E, vertex (z, true) = z.val.2 :=
    fun z => Subtype.ext (hy z).symm
  refine use_cover (exists_cell_root_cover G R a b hR M w i x
    (fun z => (hp z).1) (fun z => (hp z).2.1) hax hxy hyb
    (fun z => z.val.1.property) hne₁ D qD hD start) ?_
  intro k hk f s c hsc r hr hCover
  refine retain_result k hk r hr ?_
  intro A _ _ _
  let X : V → Over (Spec (.of k.val)) := fun t =>
    stageScalarModel R (cellArithmeticBase G a b t.val t.property (M t)) k
  let U := stageScalarModel R (𝟙 (Spec (.of R))) k
  let B := stageScalarModel R (projectiveToSpec R (ULift.{u} (Fin 2))) k
  let origin : ∀ t : V, Spec (.of k.val) ⟶ (X t).left := fun t =>
    cellArithmeticStageOrigin G a b t.val t.property (M t) k
  have hSection : ∀ t : V, origin t ≫ (X t).hom = 𝟙 _ := fun t =>
    cellArithmeticStageOrigin_base G a b t.val t.property (M t) k
  let (t : V) : GeometricallyConnected (X t).hom :=
    cellArithmeticStage_geomConnected G a b t.val t.property (M t) k
  let : GeometricallyConnected B.hom := projectiveStage_geomConnected R k
  let : IsIso U.hom := unit_model_iso
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) U rfl
  exact graph_of_edge_data r (stageScalarModel R D.hom k) rel root X f origin hSection U B
    vertex s c
    (fun t => cellArithmeticAnchorMap G a b t.val t.property (M t) D k (f t))
    (fun _ => rfl) hSource hTarget (fun z => (hsc z).1) hCover hPath

end SchubertGeometry.CellContraction
