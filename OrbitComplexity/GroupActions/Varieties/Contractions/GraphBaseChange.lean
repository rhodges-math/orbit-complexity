import Batteries.Tactic.Lint
import OrbitComplexity.GroupActions.Varieties.Contractions.GraphGluing
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Graph diagrams in every geometric fibre

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace GroupActions

universe u v

private theorem graph_section_base {S D X : Scheme.{u}}
    (d : D ⟶ S) (f : X ⟶ D) (a : X ⟶ S) (s : S ⟶ X)
    (hf : f ≫ d = a) (hs : s ≫ a = 𝟙 S) : (s ≫ f) ≫ d = 𝟙 S := by
  rw [Category.assoc, hf, hs]

private theorem graph_fibre_connected {S D X Z : Scheme.{u}}
    (d : D ⟶ S) (f : X ⟶ D) (a : X ⟶ S) (hf : f ≫ d = a)
    [GeometricallyConnected a] {L : Type u} [Field L]
    (y : Spec (.of L) ⟶ S) (q : Z ⟶ D) (b : Z ⟶ Spec (.of L))
    (h : IsPullback q b d y) : ConnectedSpace (pullback f q : Scheme.{u}) := by
  have hp : IsPullback (pullback.fst f q) (pullback.snd f q ≫ b) a y := by
    simpa only [hf] using (IsPullback.of_hasPullback f q).paste_vert h
  exact (inferInstance : GeometricallyConnected a).geometrically_connectedSpace
    y (pullback.fst f q) (pullback.snd f q ≫ b) hp

private def graph_fibre_anchor {S D X Z : Scheme.{u}}
    (d : D ⟶ S) (f : X ⟶ D) (a : X ⟶ S) (s : S ⟶ X)
    (hf : f ≫ d = a) (hs : s ≫ a = 𝟙 S)
    {T : Scheme.{u}} (y : T ⟶ S) (q : Z ⟶ D) (b : Z ⟶ T)
    (h : IsPullback q b d y) : T ⟶ Z :=
  h.lift (y ≫ (s ≫ f)) (𝟙 T) (by
    rw [Category.assoc, graph_section_base d f a s hf hs, Category.comp_id,
      Category.id_comp])

private theorem graph_anchor_fst {S D X Z T : Scheme.{u}}
    (d : D ⟶ S) (f : X ⟶ D) (a : X ⟶ S) (s : S ⟶ X)
    (hf : f ≫ d = a) (hs : s ≫ a = 𝟙 S)
    (y : T ⟶ S) (q : Z ⟶ D) (b : Z ⟶ T) (h : IsPullback q b d y) :
    graph_fibre_anchor d f a s hf hs y q b h ≫ q = y ≫ (s ≫ f) := by
  exact h.lift_fst _ _ _

private theorem graph_anchor_in_piece {S D X Z T : Scheme.{u}}
    (d : D ⟶ S) (f : X ⟶ D) (a : X ⟶ S) (s : S ⟶ X)
    (hf : f ≫ d = a) (hs : s ≫ a = 𝟙 S)
    (y : T ⟶ S) (q : Z ⟶ D) (b : Z ⟶ T) (h : IsPullback q b d y)
    (p : T) : graph_fibre_anchor d f a s hf hs y q b h p ∈
      Set.range (pullback.snd f q) := by
  let z : T ⟶ pullback f q := pullback.lift (y ≫ s)
    (graph_fibre_anchor d f a s hf hs y q b h) (by
      rw [graph_anchor_fst, Category.assoc])
  refine ⟨z p, ?_⟩
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun g : T ⟶ Z => g p) (pullback.lift_snd (y ≫ s)
      (graph_fibre_anchor d f a s hf hs y q b h) _)

private theorem graph_anchor_in_bridge {S D X B Z T : Scheme.{u}}
    (d : D ⟶ S) (f : X ⟶ D) (a : X ⟶ S) (s : S ⟶ X)
    (hf : f ≫ d = a) (hs : s ≫ a = 𝟙 S)
    (m : B ⟶ D) (t : S ⟶ B) (ht : t ≫ m = s ≫ f)
    (y : T ⟶ S) (q : Z ⟶ D) (b : Z ⟶ T) (h : IsPullback q b d y)
    (p : T) : graph_fibre_anchor d f a s hf hs y q b h p ∈
      Set.range (pullback.snd m q) := by
  let z : T ⟶ pullback m q := pullback.lift (y ≫ t)
    (graph_fibre_anchor d f a s hf hs y q b h) (by
      rw [Category.assoc, ht, graph_anchor_fst])
  refine ⟨z p, ?_⟩
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun g : T ⟶ Z => g p) (pullback.lift_snd (y ≫ t)
      (graph_fibre_anchor d f a s hf hs y q b h) _)

/-- A diagram of anchored pieces and bridges gives connected geometric fibres
of the covered scheme. The input image cover and endpoint equations pull back
as specified morphisms; no conclusion about the target's connectedness is assumed. -/
theorem geomConnected_of_graph_diagram
    {S D : Scheme.{u}} (d : D ⟶ S) {I : Type v}
    (r : I → I → Prop) (root : I)
    (X : I → Scheme.{u}) (a : ∀ i, X i ⟶ S) (piece : ∀ i, X i ⟶ D)
    (origin : ∀ i, S ⟶ X i)
    (hPiece : ∀ i, piece i ≫ d = a i)
    (hSection : ∀ i, origin i ≫ a i = 𝟙 S)
    [∀ i, GeometricallyConnected (a i)]
    (B : ∀ i j, r i j → Scheme.{u})
    (c : ∀ i j (h : r i j), B i j h ⟶ S)
    (bridge : ∀ i j (h : r i j), B i j h ⟶ D)
    (left right : ∀ i j (h : r i j), S ⟶ B i j h)
    (hBridge : ∀ i j (h : r i j), bridge i j h ≫ d = c i j h)
    [∀ i j (h : r i j), GeometricallyConnected (c i j h)]
    (hLeft : ∀ i j (h : r i j), left i j h ≫ bridge i j h = origin i ≫ piece i)
    (hRight : ∀ i j (h : r i j), right i j h ≫ bridge i j h = origin j ≫ piece j)
    (hCover : ∀ x : D, ∃ i, x ∈ Set.range (piece i))
    (hPath : ∀ i, Relation.ReflTransGen r root i) : GeometricallyConnected d := by
  constructor
  intro L hL y Z q b h
  let anchor (i : I) : Spec (.of L) ⟶ Z :=
    graph_fibre_anchor d (piece i) (a i) (origin i) (hPiece i) (hSection i) y q b h
  apply GroupActions.connectedSpace_of_graph_cover r root
    (fun i => anchor i (IsLocalRing.closedPoint L))
    (fun i => Set.range (pullback.snd (piece i) q))
  · intro i
    let : ConnectedSpace (pullback (piece i) q : Scheme.{u}) :=
      graph_fibre_connected d (piece i) (a i) (hPiece i) y q b h
    exact isPreconnected_range (pullback.snd (piece i) q).continuous
  · intro i
    exact graph_anchor_in_piece d (piece i) (a i) (origin i) (hPiece i)
      (hSection i) y q b h (IsLocalRing.closedPoint L)
  · intro z
    obtain ⟨i, x, hx⟩ := hCover (q z)
    obtain ⟨p, _, hp⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := piece i) (g := q) x z hx
    exact ⟨i, p, hp⟩
  · intro i j hij
    let : ConnectedSpace (pullback (bridge i j hij) q : Scheme.{u}) :=
      graph_fibre_connected d (bridge i j hij) (c i j hij) (hBridge i j hij) y q b h
    refine ⟨Set.range (pullback.snd (bridge i j hij) q),
      isPreconnected_range (pullback.snd (bridge i j hij) q).continuous, ?_, ?_⟩
    · exact graph_anchor_in_bridge d (piece i) (a i) (origin i) (hPiece i)
        (hSection i) (bridge i j hij) (left i j hij) (hLeft i j hij)
        y q b h (IsLocalRing.closedPoint L)
    · exact graph_anchor_in_bridge d (piece j) (a j) (origin j) (hPiece j)
        (hSection j) (bridge i j hij) (right i j hij) (hRight i j hij)
        y q b h (IsLocalRing.closedPoint L)
  · exact hPath

end GroupActions
