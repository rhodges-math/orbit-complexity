import OrbitComplexity.SchubertGeometry.Cells.RichardsonOpen
import OrbitComplexity.SchubertGeometry.Cells.SchubertActionOpen
import OrbitComplexity.GroupActions.Varieties.SmoothProducts
import OrbitComplexity.GroupActions.Varieties.ProductImmersions
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import Mathlib.Topology.LocalAtTarget

/-! # Restriction of open maps to induced intersections

The topology of a reduced closed intersection identifies the restricted action family
with the inverse image of its target Schubert variety.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u v w z

private theorem isOpenMap_induced_square
    {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (i : A → B) (j : C → D) (f : B → D) (g : A → C)
    (hi : IsEmbedding i) (hj : IsEmbedding j) (hf : IsOpenMap f)
    (hcomm : ∀ a, j (g a) = f (i a)) (hrange : Set.range i = f ⁻¹' Set.range j) :
    IsOpenMap g := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := hi.isInducing.isOpen_iff.mp hU
  apply hj.isInducing.isOpen_iff.mpr
  refine ⟨f '' V, hf V hV, ?_⟩
  ext y
  constructor
  · rintro ⟨b, hb, hby⟩
    have hbRange : b ∈ Set.range i := by
      rw [hrange]
      exact ⟨y, hby.symm⟩
    obtain ⟨a, ha⟩ := hbRange
    refine ⟨a, ?_, ?_⟩
    · rw [← hVU]
      change i a ∈ V
      rwa [ha]
    · apply hj.injective
      exact (hcomm a).trans ((congrArg f ha).trans hby)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨i a, ?_, (hcomm a).symm⟩
    have : a ∈ i ⁻¹' V := by rwa [hVU]
    exact this

section Intersections
variable {K : Type u} [Field K]

private def factorTo {A R X : Variety K} (i : A.toOver ⟶ X.toOver)
    (r : R.toOver ⟶ X.toOver) [IsPreimmersion i.left]
    (h : Set.range r.left ⊆ Set.range i.left) : R.toOver ⟶ A.toOver := by
  let r₀ : R.scheme ⟶ X.scheme := r.left
  let i₀ : A.scheme ⟶ X.scheme := i.left
  let f := GroupActions.liftPreimmersion i₀ r₀ h
  have hf : f ≫ i₀ = r₀ := GroupActions.liftPreimmersion_fac i₀ r₀ h
  exact Over.homMk f (by
    rw [← i.w, ← Category.assoc, hf]
    exact r.w)

private theorem factorTo_comp {A R X : Variety K} (i : A.toOver ⟶ X.toOver)
    (r : R.toOver ⟶ X.toOver) [IsPreimmersion i.left]
    (h : Set.range r.left ⊆ Set.range i.left) : factorTo i r h ≫ i = r := by
  apply Over.OverMorphism.ext
  let r₀ : R.scheme ⟶ X.scheme := r.left
  let i₀ : A.scheme ⟶ X.scheme := i.left
  exact GroupActions.liftPreimmersion_fac i₀ r₀ h

attribute [local irreducible] factorTo

private instance factorTo_closed {A R X : Variety K} (i : A.toOver ⟶ X.toOver)
    (r : R.toOver ⟶ X.toOver) [IsClosedImmersion i.left] [IsClosedImmersion r.left]
    (h : Set.range r.left ⊆ Set.range i.left) : IsClosedImmersion (factorTo i r h).left := by
  let f : R.scheme ⟶ A.scheme := (factorTo i r h).left
  let i₀ : A.scheme ⟶ X.scheme := i.left
  have hf : f ≫ i₀ = r.left := congrArg Over.Hom.left (factorTo_comp i r h)
  have : IsClosedImmersion (f ≫ i₀) := hf.symm ▸ inferInstance
  exact IsClosedImmersion.of_comp_isClosedImmersion f i₀

variable (H X A Y R : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver] [ModObj H.toOver A.toOver]
  (i : A.toOver ⟶ X.toOver) (j : Y.toOver ⟶ X.toOver) (r : R.toOver ⟶ X.toOver)
  [IsClosedImmersion i.left] [IsClosedImmersion j.left] [IsClosedImmersion r.left]
  [IsModHom H.toOver i]
  (hr : Set.range r.left = Set.range i.left ∩ Set.range j.left)

private def firstMap : R.toOver ⟶ A.toOver :=
  factorTo i r (by rw [hr]; exact Set.inter_subset_left)

private def secondMap : R.toOver ⟶ Y.toOver :=
  factorTo j r (by rw [hr]; exact Set.inter_subset_right)

omit [IsClosedImmersion j.left] [IsClosedImmersion r.left] in
private theorem firstMap_comp : firstMap X A Y R i j r hr ≫ i = r :=
  factorTo_comp i r _

omit [IsClosedImmersion i.left] [IsClosedImmersion r.left] in
private theorem secondMap_comp : secondMap X A Y R i j r hr ≫ j = r :=
  factorTo_comp j r _

private def intersectionFamily : H.toOver ⊗ R.toOver ⟶ A.toOver :=
  (H.toOver ◁ firstMap X A Y R i j r hr) ≫ γ[H.toOver, A.toOver]

omit [IsClosedImmersion r.left] in
private theorem intersectionFamily_square :
    intersectionFamily H X A Y R i j r hr ≫ i =
      (H.toOver ◁ secondMap X A Y R i j r hr) ≫
        (H.toOver ◁ j) ≫ γ[H.toOver, X.toOver] := by
  rw [intersectionFamily, Category.assoc, IsModHom.smul_hom]
  change (H.toOver ◁ firstMap X A Y R i j r hr) ≫ (H.toOver ◁ i) ≫
    γ[H.toOver, X.toOver] = _
  rw [← whiskerLeft_comp_assoc, firstMap_comp, ← whiskerLeft_comp_assoc, secondMap_comp]

private def sourceInclusion : H.toOver ⊗ R.toOver ⟶ H.toOver ⊗ Y.toOver :=
  H.toOver ◁ secondMap X A Y R i j r hr

omit [IsModHom H.toOver i] [IsClosedImmersion i.left]
  [ModObj H.toOver A.toOver] [ModObj H.toOver X.toOver] [GrpObj H.toOver] in
private theorem sourceInclusion_closed :
    IsClosedImmersion (sourceInclusion H X A Y R i j r hr).left := by
  have hsecond : IsClosedImmersion (secondMap X A Y R i j r hr).left := by
    dsimp only [secondMap]
    infer_instance
  change IsClosedImmersion (Limits.pullback.map _ _ _ _ (𝟙 H.scheme)
    (secondMap X A Y R i j r hr).left (𝟙 (Spec (CommRingCat.of K)))
      (by simp) (by simpa only [Category.comp_id] using
        (secondMap X A Y R i j r hr).w.symm))
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun f g hf hg => @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) (by infer_instance)
    hsecond (by simp) (secondMap X A Y R i j r hr).w.symm

omit [IsClosedImmersion i.left] in
private theorem equivariant_points (a : H.points) (q : A.points) :
    Variety.mapPoints i (a • q) = a • Variety.mapPoints i q := by
  apply X.pointsEquivOverHom.injective
  change A.pointsEquivOverHom (a • q) ≫ i =
    X.pointsEquivOverHom (a • Variety.mapPoints i q)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul i (H.pointsEquivOverHom a) (A.pointsEquivOverHom q)

variable [IsAlgClosed K] [Smooth H.toSpec]

omit [IsClosedImmersion r.left] in
private theorem sourceInclusion_range :
    Set.range (sourceInclusion H X A Y R i j r hr).left =
      ((H.toOver ◁ j) ≫ γ[H.toOver, X.toOver]).left ⁻¹' Set.range i.left := by
  let P := Variety.smoothProductVariety H Y
  let Q := Variety.smoothProductVariety H R
  let f : P.toOver ⟶ X.toOver := (H.toOver ◁ j) ≫ γ[H.toOver, X.toOver]
  let s : Q.toOver ⟶ P.toOver := sourceInclusion H X A Y R i j r hr
  have hsquare : intersectionFamily H X A Y R i j r hr ≫ i = s ≫ f :=
    intersectionFamily_square H X A Y R i j r hr
  apply Set.Subset.antisymm
  · rintro _ ⟨q, rfl⟩
    refine ⟨(intersectionFamily H X A Y R i j r hr).left q, ?_⟩
    exact congrArg (fun g : Q.scheme ⟶ X.scheme => g q)
      (congrArg Over.Hom.left hsquare)
  · let C : Closeds P.scheme := ⟨f.left ⁻¹' Set.range i.left,
      i.left.isClosedEmbedding.isClosed_range.preimage f.left.continuous⟩
    let Z := P.closedSubvariety C
    let z : Z.toOver ⟶ P.toOver := P.closedInclusion C
    have hzRange : Set.range z.left = f.left ⁻¹' Set.range i.left :=
      P.closedInclusion_range C
    rw [← hzRange]
    apply Variety.range_subset_of_mapPoints z s
    rintro _ ⟨zq, rfl⟩
    let p := Variety.mapPoints z zq
    let h := H.pointsEquivOverHom.symm
      (P.pointsEquivOverHom p ≫ fst H.toOver Y.toOver)
    let y := Y.pointsEquivOverHom.symm
      (P.pointsEquivOverHom p ≫ snd H.toOver Y.toOver)
    have hp : P.pointsEquivOverHom p =
        lift (H.pointsEquivOverHom h) (Y.pointsEquivOverHom y) := by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [lift_fst, lift_snd, h, y, Equiv.apply_symm_apply]
    have hfp : Variety.mapPoints f p = h • Variety.mapPoints j y := by
      apply X.pointsEquivOverHom.injective
      change P.pointsEquivOverHom p ≫ (H.toOver ◁ j) ≫ γ[H.toOver, X.toOver] = _
      rw [hp, lift_whiskerLeft_assoc]
      rfl
    have hpC : f.left (P.pointMap p) ∈ Set.range i.left := by
      have hzmem : P.pointMap p ∈ Set.range z.left :=
        ⟨Z.pointMap zq, rfl⟩
      rwa [hzRange] at hzmem
    have hfpRange : Variety.mapPoints f p ∈ Set.range (Variety.mapPoints i) := by
      rw [Variety.range_mapPoints]
      change X.pointMap (Variety.mapPoints f p) ∈ Set.range i.left
      rwa [Variety.pointMap_mapPoints]
    obtain ⟨a, ha⟩ := hfpRange
    have ha0 : Variety.mapPoints i (h⁻¹ • a) = Variety.mapPoints j y := by
      rw [equivariant_points H X A i, ha, hfp, inv_smul_smul]
    have hyr : X.pointMap (Variety.mapPoints j y) ∈ Set.range r.left := by
      rw [hr]
      refine ⟨⟨A.pointMap (h⁻¹ • a), ?_⟩, ⟨Y.pointMap y, rfl⟩⟩
      exact congrArg X.pointMap ha0
    obtain ⟨t, ht⟩ := Variety.exists_mapPoints_eq r (Variety.mapPoints j y) hyr
    have htY : Variety.mapPoints (secondMap X A Y R i j r hr) t = y := by
      apply (Variety.isEmbedding_mapPoints j).injective
      have hc := Variety.mapPoints_comp (X := R) (Y := Y) (Z := X)
        (secondMap X A Y R i j r hr) j t
      exact hc.symm.trans ((congrArg (fun g : R.toOver ⟶ X.toOver =>
        Variety.mapPoints g t) (secondMap_comp X A Y R i j r hr)).trans ht)
    let q := Q.pointsEquivOverHom.symm
      (lift (H.pointsEquivOverHom h) (R.pointsEquivOverHom t))
    refine ⟨q, ?_⟩
    apply P.pointsEquivOverHom.injective
    change Q.pointsEquivOverHom q ≫ (H.toOver ◁ secondMap X A Y R i j r hr) = _
    rw [Equiv.apply_symm_apply, lift_whiskerLeft]
    have htH := congrArg Y.pointsEquivOverHom htY
    change R.pointsEquivOverHom t ≫ secondMap X A Y R i j r hr =
      Y.pointsEquivOverHom y at htH
    rw [htH]
    exact hp.symm

private theorem intersectionFamily_open
    (hf : IsOpenMap ((H.toOver ◁ j) ≫ γ[H.toOver, X.toOver]).left) :
    IsOpenMap (intersectionFamily H X A Y R i j r hr).left := by
  let P := Variety.smoothProductVariety H Y
  let Q := Variety.smoothProductVariety H R
  let s : Q.scheme ⟶ P.scheme := (sourceInclusion H X A Y R i j r hr).left
  let i₀ : A.scheme ⟶ X.scheme := i.left
  let f : P.scheme ⟶ X.scheme := ((H.toOver ◁ j) ≫ γ[H.toOver, X.toOver]).left
  let g : Q.scheme ⟶ A.scheme := (intersectionFamily H X A Y R i j r hr).left
  have : IsClosedImmersion s := sourceInclusion_closed H X A Y R i j r hr
  apply isOpenMap_induced_square s i₀ f g s.isEmbedding i₀.isEmbedding hf
  · intro q
    exact congrArg (fun t : Q.scheme ⟶ X.scheme => t q)
      (congrArg Over.Hom.left (intersectionFamily_square H X A Y R i j r hr))
  · exact sourceInclusion_range H X A Y R i j r hr

end Intersections

section Richardson
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The closed Richardson intersection maps to its Schubert variety. -/
def richardsonToSchubert (u v : G.weylGroup) :
    (richardsonVariety G u v).toOver ⟶ (schubertVariety G v).toOver :=
  firstMap (flagVariety G) (schubertVariety G v) (oppositeSchubertVariety G u)
    (richardsonVariety G u v) (schubertInclusion G v) (oppositeSchubertInclusion G u)
      (richardsonInclusion G u v) (richardsonInclusion_range G u v)

/-- The closed Richardson intersection maps to its opposite Schubert variety. -/
def richardsonToOpposite (u v : G.weylGroup) :
    (richardsonVariety G u v).toOver ⟶ (oppositeSchubertVariety G u).toOver :=
  secondMap (flagVariety G) (schubertVariety G v) (oppositeSchubertVariety G u)
    (richardsonVariety G u v) (schubertInclusion G v) (oppositeSchubertInclusion G u)
      (richardsonInclusion G u v) (richardsonInclusion_range G u v)

/-- The Richardson-to-Schubert map commutes with the flag inclusions. -/
theorem richardsonToSchubert_comp (u v : G.weylGroup) :
    richardsonToSchubert G u v ≫ schubertInclusion G v = richardsonInclusion G u v :=
  firstMap_comp (flagVariety G) (schubertVariety G v) (oppositeSchubertVariety G u)
    (richardsonVariety G u v) (schubertInclusion G v) (oppositeSchubertInclusion G u)
      (richardsonInclusion G u v) (richardsonInclusion_range G u v)

/-- The Richardson-to-opposite map commutes with the flag inclusions. -/
theorem richardsonToOpposite_comp (u v : G.weylGroup) :
    richardsonToOpposite G u v ≫ oppositeSchubertInclusion G u = richardsonInclusion G u v :=
  secondMap_comp (flagVariety G) (schubertVariety G v) (oppositeSchubertVariety G u)
    (richardsonVariety G u v) (schubertInclusion G v) (oppositeSchubertInclusion G u)
      (richardsonInclusion G u v) (richardsonInclusion_range G u v)

/-- The Borel action family from a closed Richardson intersection into its Schubert variety
is open. -/
theorem borelRichardsonFamily_open (u v : G.weylGroup) :
    IsOpenMap (((borelVariety G).toOver ◁ richardsonToSchubert G u v) ≫
      γ[(borelVariety G).toOver, (schubertVariety G v).toOver]).left := by
  have : Smooth (borelVariety G).toSpec :=
    TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced
      (borelVariety G).toSpec
  exact intersectionFamily_open (borelVariety G) (flagVariety G) (schubertVariety G v)
    (oppositeSchubertVariety G u) (richardsonVariety G u v)
    (schubertInclusion G v) (oppositeSchubertInclusion G u) (richardsonInclusion G u v)
    (richardsonInclusion_range G u v) (oppositeSchubert_borel_open G u)

/-- The opposite Borel action family from a closed Richardson intersection into its opposite
Schubert variety is open. -/
theorem oppositeRichardsonFamily_open (u v : G.weylGroup) :
    IsOpenMap (((oppositeBorelVariety G).toOver ◁ richardsonToOpposite G u v) ≫
      γ[(oppositeBorelVariety G).toOver, (oppositeSchubertVariety G u).toOver]).left := by
  have : Smooth (oppositeBorelVariety G).toSpec :=
    TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced
      (oppositeBorelVariety G).toSpec
  have hr : Set.range (richardsonInclusion G u v).left =
      Set.range (oppositeSchubertInclusion G u).left ∩
        Set.range (schubertInclusion G v).left := by
    rw [richardsonInclusion_range, Set.inter_comm]
  exact intersectionFamily_open (oppositeBorelVariety G) (flagVariety G)
    (oppositeSchubertVariety G u) (schubertVariety G v) (richardsonVariety G u v)
    (oppositeSchubertInclusion G u) (schubertInclusion G v) (richardsonInclusion G u v)
    hr (schubert_oppositeBorel_open G v)

end Richardson
end
end SchubertGeometry
