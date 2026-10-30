import OrbitComplexity.GroupActions.Actions.Points
import OrbitComplexity.GroupActions.Varieties.SmoothProducts
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Dense inverse images under open action families

The inverse image of a stable dense open remains dense when its associated action family
is open. The variety mapping to the acted-on variety need not carry an action.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (H A R : Variety K) [GrpObj H.toOver] [ModObj H.toOver A.toOver] [Smooth H.toSpec]

/-- An open action family pulls a stable dense open back to a dense subset. -/
theorem dense_preimage_of_open_action (p : R.toOver ⟶ A.toOver)
    (hp : IsOpenMap ((H.toOver ◁ p) ≫ γ[H.toOver, A.toOver]).left)
    (C : A.scheme.Opens) (hCd : Dense (C : Set A.scheme))
    (hCs : ∀ (h : H.points) (x : A.points),
      A.pointMap x ∈ C → A.pointMap (h • x) ∈ C) :
    Dense (p.left ⁻¹' (C : Set A.scheme)) := by
  let P := Variety.smoothProductVariety H R
  let f : P.toOver ⟶ A.toOver := (H.toOver ◁ p) ≫ γ[H.toOver, A.toOver]
  let π : P.toOver ⟶ R.toOver := snd H.toOver R.toOver
  let s : R.toOver ⟶ P.toOver :=
    lift (1 : R.toOver ⟶ H.toOver) (𝟙 R.toOver)
  have hs : s ≫ π = 𝟙 R.toOver := lift_snd _ _
  have hd : Dense (Set.range P.pointMap) := by
    have : LocallyOfFiniteType P.toSpec := P.locallyOfFiniteType
    have : JacobsonSpace P.scheme := LocallyOfFiniteType.jacobsonSpace P.toSpec
    rw [dense_iff_closure_eq, P.pointMap_range, closure_closedPoints]
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  let V : Set P.scheme := π.left ⁻¹' U
  have hV : IsOpen V := hU.preimage π.left.continuous
  have hVne : V.Nonempty := by
    obtain ⟨r, hr⟩ := hUne
    refine ⟨s.left r, ?_⟩
    have hsr := congrArg (fun q : R.scheme ⟶ R.scheme => q r)
      (congrArg Over.Hom.left hs)
    change π.left (s.left r) = r at hsr
    change π.left (s.left r) ∈ U
    rwa [hsr]
  have hfV : IsOpen (f.left '' V) := hp V hV
  obtain ⟨a, haC, v, hvV, hva⟩ := hCd.exists_mem_open hfV (hVne.image f.left)
  let W : Set P.scheme := V ∩ f.left ⁻¹' (C : Set A.scheme)
  have hW : IsOpen W := hV.inter (C.isOpen.preimage f.left.continuous)
  have hWne : W.Nonempty := by
    refine ⟨v, hvV, ?_⟩
    change f.left v ∈ C
    rwa [hva]
  obtain ⟨_, ⟨z, rfl⟩, hzW⟩ := hd.exists_mem_open hW hWne
  let h := H.pointsEquivOverHom.symm
    (P.pointsEquivOverHom z ≫ fst H.toOver R.toOver)
  let x := Variety.mapPoints π z
  have hz : P.pointsEquivOverHom z =
      lift (H.pointsEquivOverHom h) (R.pointsEquivOverHom x) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [lift_fst, h, Equiv.apply_symm_apply]
    · rw [lift_snd]
      rfl
  have hfz : Variety.mapPoints f z = h • Variety.mapPoints p x := by
    apply A.pointsEquivOverHom.injective
    change P.pointsEquivOverHom z ≫ (H.toOver ◁ p) ≫ γ[H.toOver, A.toOver] = _
    rw [hz, lift_whiskerLeft_assoc]
    rfl
  have hxU : R.pointMap x ∈ U := hzW.1
  have hfpC : A.pointMap (h • Variety.mapPoints p x) ∈ C := by
    rw [← hfz]
    exact hzW.2
  have hpxC : A.pointMap (Variety.mapPoints p x) ∈ C := by
    simpa only [inv_smul_smul] using hCs h⁻¹ (h • Variety.mapPoints p x) hfpC
  exact ⟨R.pointMap x, hxU, hpxC⟩

end
end GroupActions
