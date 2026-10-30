import OrbitComplexity.SchubertGeometry.Deodhar.FibreFrames
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeFibrePoints
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.SchubertGeometry.Deodhar.Components
import OrbitComplexity.SchubertGeometry.Deodhar.InitialCell
import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.BruhatIntervals.SubexpressionPaths

/-! # Deodhar component covers

Opposite-cell indices along regular prefix projections form a distinguished subexpression.
The resulting finite family covers every prefix cell and each open Richardson stratum.

See R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups SchubertGeometry GroupActions
open BruhatIntervals Topology
noncomputable section
attribute [local irreducible] wordCellExtensionIso wordCellStep rankOneCellProjection
  rankOneLiftIso GroupActions.Variety.mapPoints wordCellProjection
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)
private theorem inverse_square {C : Type*} [Category C] {A B Z : C}
    (e : A ≅ B) (f : A ⟶ Z) (g : B ⟶ Z) (h : e.hom ≫ g = f) : e.inv ≫ f = g := by
  rw [← h, Iso.inv_hom_id_assoc]

private def oppositeFlags (v : G.weylGroup) : Set (flagVariety G).points :=
  Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G v))

private def ordinaryFlag (w : G.weylGroup) (x : (schubertCell G w).points) :
    (flagVariety G).points := Variety.mapPoints (schubertCellInclusion G w) x

private def fibreFlag (u : G.points) (v : G.weylGroup) (i : G.rootBase.support) (t : K) :
    (flagVariety G).points := flagVarietyPointsEquiv G (flagProjection G
      (u * G.weylPoint v * gaParameterPoint (G.simpleRootMap i) t *
        (G.reflectionPoint i.val)⁻¹))

attribute [local irreducible] oppositeFlags ordinaryFlag fibreFlag

set_option maxHeartbeats 400000 in
private theorem opposite_fibre_cases (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints)
    (v : G.weylGroup) (i : G.rootBase.support) (t : K) :
    (fibreFlag G u v i t ∈ oppositeFlags G v ∨ fibreFlag G u v i t ∈
      oppositeFlags G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val) →
      fibreFlag G u v i t ∈ oppositeFlags G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  constructor
  · by_cases hpos : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val)
    · by_cases hz : t = 0
      · subst t
        exact Or.inr (by simpa only [fibreFlag, oppositeFlags] using oppositeFibre_zero G u hu v i)
      · exact Or.inl (by simpa only [fibreFlag, oppositeFlags] using
          oppositeFibre_ascent G u hu v i hpos t hz)
    · exact Or.inr (by simpa only [fibreFlag, oppositeFlags] using
        oppositeFibre_descent G u hu v i hpos t)
  · intro hneg
    simpa only [fibreFlag, oppositeFlags] using oppositeFibre_descent G u hu v i hneg t

set_option maxHeartbeats 400000 in
private theorem rankOne_opposite_step (w : G.weylGroup) (i : G.rootBase.support)
    (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (x : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points)
    (v : G.weylGroup)
    (hv : ordinaryFlag G w (Variety.mapPoints (rankOneCellProjection G w i hi) x) ∈
      oppositeFlags G v) :
    (ordinaryFlag G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) x ∈ oppositeFlags G v ∨
      ordinaryFlag G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) x ∈
        oppositeFlags G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val) →
      ordinaryFlag G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) x ∈
        oppositeFlags G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  have hv' : ordinaryFlag G w (Variety.mapPoints (rankOneCellProjection G w i hi) x) ∈
      Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G v)) := by
    simpa only [oppositeFlags] using hv
  obtain ⟨u, hu, he⟩ := oppositeCell_unipotent_form G v _ hv'
  have he' : flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint v)) =
      Variety.mapPoints (schubertCellInclusion G w)
        (Variety.mapPoints (rankOneCellProjection G w i hi) x) := by
    simpa only [ordinaryFlag] using he.symm
  obtain ⟨t, ht⟩ := rankOneCellFibre_frame G w i hi x (u * G.weylPoint v) he'
  have ht' : ordinaryFlag G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) x =
      fibreFlag G u v i t := by simpa only [ordinaryFlag, fibreFlag] using ht
  have hcases := opposite_fibre_cases G u hu v i t
  exact (congrArg (fun q : (flagVariety G).points =>
    (q ∈ oppositeFlags G v ∨ q ∈ oppositeFlags G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val) → q ∈ oppositeFlags G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) ht').mpr hcases

set_option maxHeartbeats 400000 in
private theorem wordCell_opposite_step (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (n : ℕ) (hn : n < word.length) (x : (wordCell G word (n + 1)).points)
    (v : G.weylGroup)
    (hv : ordinaryFlag G (simpleWeylWord G.rootBase (word.take n))
      (Variety.mapPoints (wordCellStep G word hred n) x) ∈ oppositeFlags G v) :
    (ordinaryFlag G (simpleWeylWord G.rootBase (word.take (n + 1))) x ∈ oppositeFlags G v ∨
      ordinaryFlag G (simpleWeylWord G.rootBase (word.take (n + 1))) x ∈ oppositeFlags G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem word[n])) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v word[n]) →
      ordinaryFlag G (simpleWeylWord G.rootBase (word.take (n + 1))) x ∈ oppositeFlags G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem word[n])) := by
  let w := simpleWeylWord G.rootBase (word.take n)
  let i : G.rootBase.support := word[n]
  let hi := wordCell_ascent G word hred n hn
  let e := wordCellExtensionIso G word n hn
  let x' : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points :=
    Variety.mapPoints (X := wordCell G word (n + 1))
      (Y := schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) e.inv x
  have hp : Variety.mapPoints (rankOneCellProjection G w i hi) x' =
      Variety.mapPoints (wordCellStep G word hred n) x := by
    exact (Variety.mapPoints_comp (X := wordCell G word (n + 1))
      (Y := schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (Z := wordCell G word n) e.inv (rankOneCellProjection G w i hi) x).symm.trans
      (congrArg (fun f : (wordCell G word (n + 1)).toOver ⟶ (wordCell G word n).toOver =>
        Variety.mapPoints (X := wordCell G word (n + 1)) (Y := wordCell G word n) f x)
          (wordCellStep_eq G word hred n hn hi).symm)
  have hf : ordinaryFlag G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) x' =
      ordinaryFlag G (simpleWeylWord G.rootBase (word.take (n + 1))) x := by
    have hcomp : e.inv ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val) =
          schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1))) :=
      inverse_square e _ _ (wordCellExtensionIso_flag G word n hn)
    simpa only [ordinaryFlag, x'] using (Variety.mapPoints_comp (X := wordCell G word (n + 1))
      (Y := schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      (Z := flagVariety G) e.inv
      (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) x).symm.trans
      (congrArg (fun f : (wordCell G word (n + 1)).toOver ⟶ (flagVariety G).toOver =>
        Variety.mapPoints (X := wordCell G word (n + 1)) (Y := flagVariety G) f x) hcomp)
  have hv' : ordinaryFlag G w
      (Variety.mapPoints (rankOneCellProjection G w i hi) x') ∈ oppositeFlags G v := by
    exact (congrArg (fun p : (schubertCell G w).points => ordinaryFlag G w p ∈
      oppositeFlags G v) hp).mpr hv
  have h := rankOne_opposite_step G w i hi x' v hv'
  exact (congrArg (fun q : (flagVariety G).points =>
    (q ∈ oppositeFlags G v ∨ q ∈ oppositeFlags G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v i.val) → q ∈ oppositeFlags G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))) hf).mp h

private theorem opposite_index_eq {v w : G.weylGroup} {q : (flagVariety G).points}
    (hv : q ∈ oppositeFlags G v) (hw : q ∈ oppositeFlags G w) : v = w := by
  simp only [oppositeFlags, oppositeSchubertCell_points_range] at hv hw
  exact oppositeSchubertOrbits_disjoint G hv hw

private theorem initialCell_points (x : (schubertCell G 1).points) :
    Variety.mapPoints (schubertCellInclusion G 1) x = weylFlagPoint G 1 := by
  obtain ⟨p, hp⟩ := (Variety.pointsHomeomorph (initialCellIso G)).surjective x
  rw [← hp]
  change Variety.mapPoints (schubertCellInclusion G 1)
    (Variety.mapPoints (initialCellIso G).hom p) = _
  rw [← Variety.mapPoints_comp, initialCellIso_points]
  rw [weylFlagPoint, G.weylPoint_eq, weylElementPoint_one]

private theorem opposite_cover (q : (flagVariety G).points) : ∃ v, q ∈ oppositeFlags G v := by
  obtain ⟨v, hv⟩ := oppositeSchubertOrbits_cover G q
  exact ⟨v, by simpa only [oppositeFlags, oppositeSchubertCell_points_range] using hv⟩

private def prefixFlag (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : ℕ)
    (x : (wordCell G word n).points) (k : ℕ) : (flagVariety G).points :=
  if hk : k ≤ n then Variety.mapPoints
    (wordCellProjection G word hred hk ≫
      schubertCellInclusion G (simpleWeylWord G.rootBase (word.take k))) x
  else weylFlagPoint G 1

attribute [local irreducible] prefixFlag

private theorem prefixFlag_zero (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : ℕ)
    (x : (wordCell G word n).points) : prefixFlag G word hred n x 0 = weylFlagPoint G 1 := by
  simp only [prefixFlag, dite_eq_left (Nat.zero_le n), Variety.mapPoints_comp]
  exact initialCell_points G _

set_option maxHeartbeats 400000 in
private theorem prefixFlag_step (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (n : ℕ)
    (x : (wordCell G word n).points) (j : ℕ) (hj : j < n) (hjw : j < word.length)
    (v : G.weylGroup) (hv : prefixFlag G word hred n x j ∈ oppositeFlags G v) :
    (prefixFlag G word hred n x (j + 1) ∈ oppositeFlags G v ∨
      prefixFlag G word hred n x (j + 1) ∈ oppositeFlags G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem word[j])) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v word[j]) →
      prefixFlag G word hred n x (j + 1) ∈ oppositeFlags G
        (v * RootPairing.weylGroup.ofIdx G.rootSystem word[j])) := by
  let hjs : j + 1 ≤ n := Nat.succ_le_of_lt hj
  let z := Variety.mapPoints (wordCellProjection G word hred hjs) x
  have hnew : prefixFlag G word hred n x (j + 1) = ordinaryFlag G
      (simpleWeylWord G.rootBase (word.take (j + 1))) z := by
    simp only [prefixFlag, dite_eq_left hjs, ordinaryFlag, Variety.mapPoints_comp, z]
  have hp : wordCellProjection G word hred hj.le =
      wordCellProjection G word hred hjs ≫ wordCellStep G word hred j := by
    have ht := wordCellProjection_trans G word hred (Nat.le_succ j) hjs
    have hs := wordCellProjection_succ G word hred (Nat.le_refl j)
    rw [wordCellProjection_self, Category.comp_id] at hs
    exact ht.trans (congrArg (fun f : (wordCell G word (j + 1)).toOver ⟶
      (wordCell G word j).toOver => wordCellProjection G word hred hjs ≫ f) hs)
  have hold : prefixFlag G word hred n x j = ordinaryFlag G
      (simpleWeylWord G.rootBase (word.take j))
      (Variety.mapPoints (wordCellStep G word hred j) z) := by
    simp only [prefixFlag, dite_eq_left hj.le, ordinaryFlag]
    rw [hp, Category.assoc, Variety.mapPoints_comp, Variety.mapPoints_comp]
  have hv' := (congrArg (fun q : (flagVariety G).points => q ∈ oppositeFlags G v) hold).mp hv
  have h := wordCell_opposite_step G word hred j hjw z v hv'
  exact (congrArg (fun q : (flagVariety G).points =>
    (q ∈ oppositeFlags G v ∨ q ∈ oppositeFlags G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem word[j])) ∧
    (¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm v word[j]) → q ∈ oppositeFlags G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem word[j]))) hnew).mpr h

private theorem descent_not_pos (w : G.weylGroup) (i : G.rootBase.support)
    (hd : (weylCoxeterSystem G.rootBase).IsRightDescent w i) :
    ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) := by
  intro hpos
  have hinc := rootInversionCount_mul_simple_of_pos G.rootBase w i hpos
  change (weylCoxeterSystem G.rootBase).length
    (w * (weylCoxeterSystem G.rootBase).simple i) <
      (weylCoxeterSystem G.rootBase).length w at hd
  simp only [weylCoxeterSystem_simple, weylCoxeterSystem_length] at hd
  omega

set_option maxHeartbeats 400000 in
/-- Every rational prefix-cell flag belongs to a distinguished intrinsic prefix component. -/
theorem deodharPrefix_points_cover (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (n : ℕ) (hn : n ≤ word.length) (x : (wordCell G word n).points) :
    ∃ expression : Subexpression word, IsDistinguished (weylCoxeterSystem G.rootBase) expression ∧
      x ∈ Set.range (Variety.mapPoints (deodharPrefixInclusion G expression hred n)) := by
  classical
  let q := prefixFlag G word hred n x
  let v (k : ℕ) : G.weylGroup := Classical.choose (opposite_cover G (q k))
  have hv (k : ℕ) : q k ∈ oppositeFlags G (v k) :=
    Classical.choose_spec (opposite_cover G (q k))
  have hzero : v 0 = 1 := by
    have hmem := hv 0
    change prefixFlag G word hred n x 0 ∈ oppositeFlags G (v 0) at hmem
    rw [prefixFlag_zero] at hmem
    apply opposite_index_eq G hmem
    simpa only [oppositeFlags, oppositeSchubertCell_points_range] using
      (MulAction.mem_orbit_self (weylFlagPoint G 1) : weylFlagPoint G 1 ∈
        MulAction.orbit (oppositeBorelVariety G).points (weylFlagPoint G 1))
  have hgeom (j : ℕ) (hj : j < n) :=
    prefixFlag_step G word hred n x j hj (hj.trans_le hn) (v j) (hv j)
  have hstep (j : ℕ) (hj : j < n) : v (j + 1) = v j ∨
      v (j + 1) = v j * (weylCoxeterSystem G.rootBase).simple (word[j]'(hj.trans_le hn)) := by
    rcases (hgeom j hj).1 with hstay | hreflect
    · exact Or.inl (opposite_index_eq G (hv (j + 1)) hstay)
    · exact Or.inr (by simpa only [weylCoxeterSystem_simple] using
        opposite_index_eq G (hv (j + 1)) hreflect)
  have hforce (j : ℕ) (hj : j < n)
      (hd : (weylCoxeterSystem G.rootBase).IsRightDescent (v j) (word[j]'(hj.trans_le hn))) :
      v (j + 1) = v j * (weylCoxeterSystem G.rootBase).simple (word[j]'(hj.trans_le hn)) := by
    have hneg := descent_not_pos G (v j) (word[j]'(hj.trans_le hn)) hd
    simpa only [weylCoxeterSystem_simple] using
      opposite_index_eq G (hv (j + 1)) ((hgeom j hj).2 hneg)
  obtain ⟨expression, hd, he⟩ := exists_distinguished_prefix
    (weylCoxeterSystem G.rootBase) word n hn v hzero hstep hforce
  refine ⟨expression, hd, (mem_deodharPrefix_points G expression hred n x).mpr ?_⟩
  intro k
  rw [he k.val (Nat.le_of_lt_succ k.isLt)]
  have h := hv k.val
  simpa only [q, prefixFlag, dite_eq_left (Nat.le_of_lt_succ k.isLt), oppositeFlags] using h

omit [CharZero K] in
private theorem finite_point_images_cover {ι : Type*} [Finite ι] (A : Variety K)
    (B : ι → Variety K) (f : ∀ i, (B i).toOver ⟶ A.toOver)
    (hf : ∀ x : A.points, ∃ i, ∃ z : (B i).points, Variety.mapPoints (f i) z = x) :
    (⋃ i, Set.range (f i).left) = Set.univ := by
  classical
  have : JacobsonSpace A.toOver.left := LocallyOfFiniteType.jacobsonSpace A.toSpec
  apply GroupActions.constructible_eq
    (IsConstructible.iUnion (fun i => Variety.isConstructible_range (f i))) .univ
  ext p
  constructor
  · rintro ⟨_, hclosed⟩
    exact ⟨Set.mem_univ p, hclosed⟩
  · rintro ⟨_, hclosed⟩
    have hp : p ∈ Set.range A.pointMap := by
      rw [Variety.pointMap_range]
      exact hclosed
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨i, z, hz⟩ := hf x
    refine ⟨Set.mem_iUnion.mpr ⟨i, ?_⟩, hclosed⟩
    refine ⟨(B i).pointMap z, ?_⟩
    rw [← Variety.pointMap_mapPoints, hz]

set_option maxHeartbeats 400000 in
/-- Distinguished intrinsic components cover every scheme point of a reduced prefix cell. -/
theorem deodharPrefix_supports_cover (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (n : ℕ) (hn : n ≤ word.length) :
    (⋃ expression : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e},
      Set.range (deodharPrefixInclusion G expression.val hred n).left) = Set.univ := by
  classical
  apply finite_point_images_cover (wordCell G word n)
    (fun expression : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e}
      => deodharPrefixComponent G expression.val hred n)
    (fun expression => deodharPrefixInclusion G expression.val hred n)
  intro x
  obtain ⟨expression, hd, z, hz⟩ := deodharPrefix_points_cover G word hred n hn x
  exact ⟨⟨expression, hd⟩, z, hz⟩

private theorem flagCell_range_eq {a b : G.weylGroup} (h : a = b) :
    Set.range (schubertCellInclusion G a).left =
      Set.range (schubertCellInclusion G b).left := by
  subst b
  rfl

/-- Distinguished Deodhar components cover the ordinary cell by their flag images. -/
theorem deodharInclusions_cover (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    (⋃ e : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e},
      Set.range (deodharInclusion G e.val hred).left) =
        Set.range (schubertCellInclusion G (simpleWeylWord G.rootBase word)).left := by
  let i := schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))
  have he (e : Subexpression word) : Set.range (deodharInclusion G e hred).left =
      i.left '' Set.range (deodharPrefixInclusion G e hred word.length).left := by
    rw [← Set.range_comp]
    rfl
  simp_rw [he]
  rw [← Set.image_iUnion, deodharPrefix_supports_cover G word hred word.length (le_refl _),
    Set.image_univ]
  exact flagCell_range_eq G (congrArg (simpleWeylWord G.rootBase)
    (show word.take word.length = word from List.take_length))

private theorem deodhar_final_points {word : List G.rootBase.support}
    (e : Subexpression word) (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (x : (deodharComponent G e hred).points) :
    Variety.mapPoints (deodharInclusion G e hred) x ∈
      Set.range (Variety.mapPoints (oppositeSchubertCellInclusion G
        (e.prefixProd (weylCoxeterSystem G.rootBase) word.length))) := by
  let y : (wordCell G word word.length).points :=
    Variety.mapPoints (deodharPrefixInclusion G e hred word.length) x
  have hc := Variety.mapPoints_comp (X := deodharComponent G e hred)
    (Y := wordCell G word word.length) (Z := flagVariety G)
    (deodharPrefixInclusion G e hred word.length)
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))) x
  have hx := (mem_deodharPrefix_points G e hred word.length y).mp ⟨x, rfl⟩
  have hop := hx (Fin.last word.length)
  rw [wordCellProjection_self G word hred word.length, Category.id_comp] at hop
  change Variety.mapPoints
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length))) y ∈ _ at hop
  rw [← hc] at hop
  exact hop

private theorem deodhar_final_range {word : List G.rootBase.support}
    (e : Subexpression word) (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    Set.range (deodharInclusion G e hred).left ⊆
      Set.range (oppositeSchubertCellInclusion G
        (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)).left := by
  apply Variety.range_subset_of_mapPoints
  rintro _ ⟨x, rfl⟩
  exact deodhar_final_points G e hred x

private theorem cover_intersection {ι W X : Type*} (P : ι → Prop)
    (S : ι → Set X) (C : Set X) (O : W → Set X) (index : ι → W)
    (hcover : (⋃ i : {i : ι // P i}, S i.val) = C)
    (hmem : ∀ i, S i ⊆ O (index i))
    (hdis : ∀ {a b : W} {x : X}, x ∈ O a → x ∈ O b → a = b) (w : W) :
    (⋃ i : {i : ι // P i ∧ index i = w}, S i.val) = C ∩ O w := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    constructor
    · rw [← hcover]
      exact Set.mem_iUnion.mpr ⟨⟨i.val, i.property.1⟩, hi⟩
    · exact i.property.2 ▸ hmem i.val hi
  · intro hx
    have hc := hx.1
    rw [← hcover] at hc
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    exact Set.mem_iUnion.mpr ⟨⟨i.val, i.property, hdis (hmem i.val hi) hx.2⟩, hi⟩

set_option maxHeartbeats 400000 in
/-- The components with final product v cover exactly the open Richardson stratum. -/
theorem deodharRichardson_cover (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (v : G.weylGroup) :
    (⋃ e : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
        e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v},
      Set.range (deodharInclusion G e.val hred).left) =
        Set.range (richardsonCellInclusion G v (simpleWeylWord G.rootBase word)).left := by
  rw [richardsonCellInclusion_range]
  exact cover_intersection (IsDistinguished (weylCoxeterSystem G.rootBase))
    (fun e : Subexpression word => Set.range (deodharInclusion G e hred).left)
    (Set.range (schubertCellInclusion G (simpleWeylWord G.rootBase word)).left)
    (fun w : G.weylGroup => Set.range (oppositeSchubertCellInclusion G w).left)
    (fun e : Subexpression word => e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
    (deodharInclusions_cover G word hred) (fun e => deodhar_final_range G e hred)
    (fun ha hb => oppositeSchubertCells_disjoint G ha hb) v

end SchubertGeometry
