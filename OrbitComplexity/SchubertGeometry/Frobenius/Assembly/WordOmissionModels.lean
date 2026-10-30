import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Pullback models of omitted-letter boundaries

The model of an earlier omitted-letter boundary in an appended word is the
pullback of its preceding model along the appended word projection.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open private familyCast erase_append_before erase_append_last priorIndex lastIndex
  source_cartesian cartesian_first_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction

namespace SchubertGeometry

private def boundaryModelMap {D : Type u} [Category.{v} D]
    {U X V Y T S W : D}
    (f : U ⟶ X) (h : U ⟶ V) (a : X ⟶ Y) (b : V ⟶ Y)
    (m : X ⟶ T) (m₀ : Y ⟶ S) (n : V ⟶ W) (q : T ⟶ S) (d : W ⟶ S)
    [HasPullback q d]
    (hf : f ≫ a = h ≫ b) (hm : m ≫ q = a ≫ m₀) (hb : b ≫ m₀ = n ≫ d) :
    U ⟶ pullback q d :=
  pullback.lift (f ≫ m) (h ≫ n) (by
    calc
      (f ≫ m) ≫ q = f ≫ (m ≫ q) := Category.assoc _ _ _
      _ = f ≫ (a ≫ m₀) := congrArg (fun t => f ≫ t) hm
      _ = (f ≫ a) ≫ m₀ := (Category.assoc _ _ _).symm
      _ = (h ≫ b) ≫ m₀ := congrArg (fun t => t ≫ m₀) hf
      _ = h ≫ (b ≫ m₀) := Category.assoc _ _ _
      _ = h ≫ (n ≫ d) := congrArg (fun t => h ≫ t) hb
      _ = (h ≫ n) ≫ d := (Category.assoc _ _ _).symm)

private theorem boundaryModelMap_fst {D : Type u} [Category.{v} D]
    {U X V Y T S W : D}
    (f : U ⟶ X) (h : U ⟶ V) (a : X ⟶ Y) (b : V ⟶ Y)
    (m : X ⟶ T) (m₀ : Y ⟶ S) (n : V ⟶ W) (q : T ⟶ S) (d : W ⟶ S)
    [HasPullback q d]
    (hf : f ≫ a = h ≫ b) (hm : m ≫ q = a ≫ m₀) (hb : b ≫ m₀ = n ≫ d) :
    boundaryModelMap f h a b m m₀ n q d hf hm hb ≫ pullback.fst q d = f ≫ m := by
  simp only [boundaryModelMap, pullback.lift_fst]

private theorem boundaryModelMap_snd {D : Type u} [Category.{v} D]
    {U X V Y T S W : D}
    (f : U ⟶ X) (h : U ⟶ V) (a : X ⟶ Y) (b : V ⟶ Y)
    (m : X ⟶ T) (m₀ : Y ⟶ S) (n : V ⟶ W) (q : T ⟶ S) (d : W ⟶ S)
    [HasPullback q d]
    (hf : f ≫ a = h ≫ b) (hm : m ≫ q = a ≫ m₀) (hb : b ≫ m₀ = n ≫ d) :
    boundaryModelMap f h a b m m₀ n q d hf hm hb ≫ pullback.snd q d = h ≫ n := by
  simp only [boundaryModelMap, pullback.lift_snd]

private theorem boundaryModelMap_cartesian {D : Type u} [Category.{v} D]
    {U X V Y T S W : D}
    (f : U ⟶ X) (h : U ⟶ V) (a : X ⟶ Y) (b : V ⟶ Y)
    (m : X ⟶ T) (m₀ : Y ⟶ S) (n : V ⟶ W) (q : T ⟶ S) (d : W ⟶ S)
    [HasPullback q d]
    (hp : IsPullback f h a b) (hm : m ≫ q = a ≫ m₀)
    (hb : IsPullback b n m₀ d) :
    IsPullback f (boundaryModelMap f h a b m m₀ n q d hp.w hm hb.w)
      m (pullback.fst q d) := by
  apply IsPullback.flip
  apply IsPullback.of_right ?_ (boundaryModelMap_fst f h a b m m₀ n q d hp.w hm hb.w)
    (IsPullback.of_hasPullback q d).flip
  rw [boundaryModelMap_snd, hm]
  exact (hp.paste_vert hb).flip

private theorem section_cartesian {D : Type u} [Category.{v} D]
    {X B Y A : D} (π : X ⟶ B) (m : X ⟶ Y) (q : Y ⟶ A) (b : B ⟶ A)
    (hp : IsPullback π m b q) (d : B ⟶ X) (δ : A ⟶ Y)
    (hd : d ≫ π = 𝟙 B) (hδ : δ ≫ q = 𝟙 A) (hm : d ≫ m = b ≫ δ) :
    IsPullback d b m δ := by
  apply IsPullback.of_right ?_ hm hp
  rw [hd, hδ]
  exact IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- A model of an omitted-letter boundary pulls back to a model of the same
boundary after appending one simple correspondence. -/
theorem bsdhOmitModel_cartesian (w : List G.rootBase.support) (i : G.rootBase.support)
    (k : Fin w.length) {Y₀ Y Z : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hm : m ≫ q = bsdhAppendFst G w i ≫ m₀)
    (d : Z ⟶ Y₀) (n : bsdhScheme G (w.eraseIdx k.val) ⟶ Z)
    (hn : IsPullback (bsdhOmitMap G w k) n m₀ d) :
    ∃ n' : bsdhScheme G ((w ++ [i]).eraseIdx k.val) ⟶ pullback q d,
      IsPullback (bsdhOmitMap G (w ++ [i]) (priorIndex G w i k)) n' m
        (pullback.fst q d) ∧
      n' ≫ pullback.snd q d =
        (familyCast (bsdhScheme G) (erase_append_before w i k.val k.isLt) ≫
          bsdhAppendFst G (w.eraseIdx k.val) i) ≫ n := by
  let h := bsdhOmitMap_cartesian G w i k
  exact ⟨boundaryModelMap _ _ _ _ m m₀ n q d h.w hm hn.w,
    boundaryModelMap_cartesian _ _ _ _ m m₀ n q d h hm hn,
    boundaryModelMap_snd _ _ _ _ m m₀ n q d h.w hm hn.w⟩

/-- The section in an append model is a pullback model of the last omitted-letter
boundary. -/
theorem bsdhLastModel_cartesian (w : List G.rootBase.support) (i : G.rootBase.support)
    {Y₀ Y : Scheme.{u}} (q : Y ⟶ Y₀)
    (m : bsdhScheme G (w ++ [i]) ⟶ Y) (m₀ : bsdhScheme G w ⟶ Y₀)
    (hmodel : IsPullback m (bsdhAppendFst G w i) q m₀)
    (δ : Y₀ ⟶ Y) (hδ : δ ≫ q = 𝟙 Y₀)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w)
    (hdm : d ≫ m = m₀ ≫ δ) :
    IsPullback (bsdhOmitMap G (w ++ [i]) (lastIndex G w i))
      (familyCast (bsdhScheme G) (erase_append_last w i) ≫ m₀) m δ :=
  cartesian_first_eq (bsdhOmitMap_last_eq G w i d hdπ hdτ)
    (source_cartesian
      (section_cartesian (bsdhAppendFst G w i) m q m₀ hmodel.flip d δ hdπ hδ hdm)
      (eqToIso (congrArg (bsdhScheme G) (erase_append_last w i))))

end SchubertGeometry
