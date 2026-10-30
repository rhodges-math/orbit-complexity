import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordOmissionModels
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The indexed family of omitted-letter boundary models

The earlier boundaries of an appended word are pullbacks of the preceding
boundaries. Its last boundary is the section of the appended projection.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v z

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open private chooseCase chooseCase_left chooseCase_right familyCast
  erase_append_last priorIndex lastIndex from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction

namespace SchubertGeometry

private def indexTransport {Idx : Sort v} (F : Idx → Sort z) {a b : Idx}
    (h : a = b) (x : F a) : F b :=
  h ▸ x

private theorem indexTransport_value {Idx : Sort v} (F : Idx → Sort z)
    {T : Sort*} (value : ∀ a, F a → T) {a b : Idx} (h : a = b) (x : F a) :
    value b (indexTransport F h x) = value a x := by
  cases h
  rfl

private theorem pullback_boundary_cartesian {C : Type u} [Category.{v} C]
    {A X B Y Z : C} (i : A ⟶ X) (n : A ⟶ B) (m : X ⟶ Y) (r : B ⟶ Y)
    (h : IsPullback i n m r) (q : Z ⟶ Y) [HasPullback q r]
    (m' : X ⟶ Z) (hm : m' ≫ q = m) :
    ∃ n' : A ⟶ pullback q r,
      IsPullback i n' m' (pullback.fst q r) ∧ n' ≫ pullback.snd q r = n := by
  let n' : A ⟶ pullback q r := pullback.lift (i ≫ m') n (by
    rw [Category.assoc, hm]
    exact h.w)
  have hf : n' ≫ pullback.fst q r = i ≫ m' := pullback.lift_fst _ _ _
  have hs : n' ≫ pullback.snd q r = n := pullback.lift_snd _ _ _
  have houter : IsPullback i (n' ≫ pullback.snd q r) (m' ≫ q) r := by
    simpa only [hs, hm] using h
  exact ⟨n', houter.of_bot hf.symm (IsPullback.of_hasPullback q r), hs⟩

private theorem pullback_earlier_cartesian {Y₀ Y Z : Scheme.{u}}
    (q : Y ⟶ Y₀) (qStage : Z ⟶ Y) (B : Over Y₀) (A : Over Y)
    (hA : A = Over.mk (pullback.fst q B.hom)) :
    ∃ p : pullback qStage A.hom ⟶ B.left,
      IsPullback (pullback.fst qStage A.hom) p (qStage ≫ q) B.hom := by
  cases hA
  exact ⟨pullback.snd qStage (pullback.fst q B.hom) ≫ pullback.snd q B.hom,
    (IsPullback.of_hasPullback qStage (pullback.fst q B.hom)).paste_vert
      (IsPullback.of_hasPullback q B.hom)⟩

private theorem pullback_last_cartesian {Y₀ Y Z : Scheme.{u}}
    (qStage : Z ⟶ Y) (δ : Y₀ ⟶ Y) (A : Over Y) (hA : A = Over.mk δ) :
    ∃ p : pullback qStage A.hom ⟶ Y₀,
      IsPullback (pullback.fst qStage A.hom) p qStage δ := by
  cases hA
  exact ⟨pullback.snd qStage δ, IsPullback.of_hasPullback qStage δ⟩

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

private structure BoundaryModel (w : List G.rootBase.support) {Y : Scheme.{u}}
    (m : bsdhScheme G w ⟶ Y) (k : Fin w.length) where
  boundary : Over Y
  closed : IsClosedImmersion boundary.hom
  comparison : bsdhScheme G (w.eraseIdx k.val) ⟶ boundary.left
  cartesian : IsPullback (bsdhOmitMap G w k) comparison m boundary.hom

private def earlierBoundary {Y Y₀ : Scheme.{u}} (q : Y ⟶ Y₀) (B : Over Y₀) : Over Y :=
  Over.mk (pullback.fst q B.hom)

private theorem earlierBoundary_closed {Y Y₀ : Scheme.{u}}
    (q : Y ⟶ Y₀) (B : Over Y₀) [IsClosedImmersion B.hom] :
    IsClosedImmersion (earlierBoundary q B).hom := by
  change IsClosedImmersion (pullback.fst q B.hom)
  infer_instance

private def boundaryBefore (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hm : m ≫ q = bsdhAppendFst G w i ≫ m₀)
    (k : Fin w.length) (B : BoundaryModel G w m₀ k) :
    BoundaryModel G (w ++ [i]) m (priorIndex G w i k) := by
  let H := bsdhOmitModel_cartesian G w i k q m m₀ hm B.boundary.hom
    B.comparison B.cartesian
  let : IsClosedImmersion B.boundary.hom := B.closed
  exact ⟨earlierBoundary q B.boundary, earlierBoundary_closed q B.boundary,
    Classical.choose H, (Classical.choose_spec H).1⟩

private def boundaryLast (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ) :
    BoundaryModel G (w ++ [i]) m (lastIndex G w i) :=
  ⟨Over.mk δ, hδclosed, familyCast (bsdhScheme G) (erase_append_last w i) ≫ m₀,
    bsdhLastModel_cartesian G w i q m m₀ hmodel δ hδ d hdπ hdτ hdm⟩

private def boundaryBeforeAt (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hm : m ≫ q = bsdhAppendFst G w i ≫ m₀)
    (B : ∀ k, BoundaryModel G w m₀ k)
    (k : Fin (w ++ [i]).length) (hk : k.val < w.length) :
    BoundaryModel G (w ++ [i]) m k :=
  boundaryBefore G w i q m m₀ hm ⟨k.val, hk⟩ (B ⟨k.val, hk⟩)

private theorem lastIndex_eq (w : List G.rootBase.support) (i : G.rootBase.support)
    (k : Fin (w ++ [i]).length) (hk : ¬k.val < w.length) :
    lastIndex G w i = k := by
  apply Fin.ext
  have hle : k.val ≤ w.length := Nat.le_of_lt_succ (by
    simpa only [List.length_append, List.length_singleton] using k.isLt)
  exact (Nat.le_antisymm hle (Nat.le_of_not_gt hk)).symm

private def boundaryLastAt (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ)
    (k : Fin (w ++ [i]).length) (hk : ¬k.val < w.length) :
    BoundaryModel G (w ++ [i]) m k :=
  indexTransport (BoundaryModel G (w ++ [i]) m) (lastIndex_eq G w i k hk)
    (boundaryLast G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm)

private theorem boundaryLastAt_over (w : List G.rootBase.support)
    (i : G.rootBase.support) {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ)
    (k : Fin (w ++ [i]).length) (hk : ¬k.val < w.length) :
    (boundaryLastAt G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm k hk).boundary =
      Over.mk δ :=
  indexTransport_value (BoundaryModel G (w ++ [i]) m) (fun _ b => b.boundary)
    (lastIndex_eq G w i k hk)
    (boundaryLast G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm)

private def appendBoundaryModels (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ) (B : ∀ k, BoundaryModel G w m₀ k)
    (k : Fin (w ++ [i]).length) : BoundaryModel G (w ++ [i]) m k :=
  chooseCase (k.val < w.length)
    (boundaryBeforeAt G w i q m m₀ hmodel.w B k)
    (boundaryLastAt G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm k)

private theorem appendBoundaryModels_before (w : List G.rootBase.support)
    (i : G.rootBase.support) {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ) (B : ∀ k, BoundaryModel G w m₀ k)
    (k : Fin w.length) :
    (appendBoundaryModels G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm B
      (priorIndex G w i k)).boundary = earlierBoundary q (B k).boundary :=
  congrArg (fun b : BoundaryModel G (w ++ [i]) m (priorIndex G w i k) => b.boundary)
    (chooseCase_left ((priorIndex G w i k).val < w.length)
      (boundaryBeforeAt G w i q m m₀ hmodel.w B (priorIndex G w i k))
      (boundaryLastAt G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm
        (priorIndex G w i k)) k.isLt)

private theorem appendBoundaryModels_last (w : List G.rootBase.support)
    (i : G.rootBase.support) {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ) (B : ∀ k, BoundaryModel G w m₀ k) :
    (appendBoundaryModels G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm B
      (lastIndex G w i)).boundary = Over.mk δ :=
  (congrArg (fun b : BoundaryModel G (w ++ [i]) m (lastIndex G w i) => b.boundary)
    (chooseCase_right ((lastIndex G w i).val < w.length)
      (boundaryBeforeAt G w i q m m₀ hmodel.w B (lastIndex G w i))
      (boundaryLastAt G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm
        (lastIndex G w i)) (Nat.lt_irrefl w.length))).trans
    (boundaryLastAt_over G w i q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm
      (lastIndex G w i) (Nat.lt_irrefl w.length))

/-- Omitted-letter models pull back along any stage map through the append
model. Their comparisons are Cartesian over the preceding boundaries and the
same omitted-last section. -/
theorem exists_word_boundary_models (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀) (hδclosed : IsClosedImmersion δ)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ)
    (B : Fin w.length → Over Y₀) (hB : ∀ k, IsClosedImmersion (B k).hom)
    (n : ∀ k, bsdhScheme G (w.eraseIdx k.val) ⟶ (B k).left)
    (hn : ∀ k, IsPullback (bsdhOmitMap G w k) (n k) m₀ (B k).hom)
    {Y' : Scheme.{u}} (qStage : Y' ⟶ Y)
    (m' : bsdhScheme G (w ++ [i]) ⟶ Y') (hm' : m' ≫ qStage = m) :
    ∃ B' : Fin (w ++ [i]).length → Over Y',
      (∀ k, IsClosedImmersion (B' k).hom) ∧
      (∃ n' : ∀ k, bsdhScheme G ((w ++ [i]).eraseIdx k.val) ⟶ (B' k).left,
        ∀ k, IsPullback (bsdhOmitMap G (w ++ [i]) k) (n' k) m' (B' k).hom) ∧
      (∀ k, B' (priorIndex G w i k) =
        Over.mk (pullback.fst qStage (pullback.fst q (B k).hom))) ∧
      B' (lastIndex G w i) = Over.mk (pullback.fst qStage δ) ∧
      (∃ p : ∀ k, (B' (priorIndex G w i k)).left ⟶ (B k).left,
        ∀ k, IsPullback (B' (priorIndex G w i k)).hom (p k)
          (qStage ≫ q) (B k).hom) ∧
      ∃ p : (B' (lastIndex G w i)).left ⟶ Y₀,
        IsPullback (B' (lastIndex G w i)).hom p qStage δ := by
  let b : ∀ k, BoundaryModel G w m₀ k := fun k => ⟨B k, hB k, n k, hn k⟩
  let b' := @appendBoundaryModels.{u} K kField kClosed kZero G w i
    Y₀ Y q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm b
  let family : Fin (w ++ [i]).length → Over Y' :=
    fun k => earlierBoundary qStage (b' k).boundary
  have hclosed : ∀ k, IsClosedImmersion (family k).hom := by
    intro k
    let : IsClosedImmersion (b' k).boundary.hom := (b' k).closed
    exact earlierBoundary_closed qStage (b' k).boundary
  have hfield := fun k => pullback_boundary_cartesian
    (bsdhOmitMap G (w ++ [i]) k) (b' k).comparison m (b' k).boundary.hom
    (b' k).cartesian qStage m' hm'
  choose n' hn' _hprojection using hfield
  have hbefore := fun k => @appendBoundaryModels_before.{u} K kField kClosed kZero
    G w i Y₀ Y q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm b k
  have hlast := @appendBoundaryModels_last.{u} K kField kClosed kZero
    G w i Y₀ Y q m m₀ hmodel δ hδ hδclosed d hdπ hdτ hdm b
  have hbeforeMaps := fun k => pullback_earlier_cartesian q qStage (B k)
    (b' (priorIndex G w i k)).boundary (hbefore k)
  choose pBefore hpBefore using hbeforeMaps
  obtain ⟨pLast, hpLast⟩ := pullback_last_cartesian qStage δ
    (b' (lastIndex G w i)).boundary hlast
  refine ⟨family, hclosed, ⟨n', hn'⟩, ?_, ?_, ⟨pBefore, hpBefore⟩, pLast, hpLast⟩
  · intro k
    exact congrArg (earlierBoundary qStage) (hbefore k)
  · exact congrArg (earlierBoundary qStage) hlast

end SchubertGeometry
