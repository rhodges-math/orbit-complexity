import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons

/-! # Common affine coordinate presentations for finite chart intersections -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem intersection_coordinate_lifts {X : Scheme.{u}} {K : Type u}
    [CommRing K] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (𝒰 : X.OpenCover.{u})
    (hU : ∀ j, IsAffine (𝒰.X j)) (s : {s : Finset 𝒰.I₀ // s.Nonempty}) :
    let W := (intersectionOpens (fun j ↦ (𝒰.f j).opensRange)).obj (.op s)
    let T : Over (Spec (.of K)) := Over.mk (W.ι ≫ base)
    let A := ((algΓ (.of K)).obj T).unop
    ∃ (a : (algSpec (.of K)).obj (.op A) ≅ T),
      a.inv = (algΓAlgSpecAdjunction (.of K)).unit.app T ∧
      ∃ p : ∀ j ∈ s.val,
          (algSpec (.of K)).obj (.op A) ⟶ Over.mk (𝒰.f j ≫ base),
        ∀ j hj, (p j hj).left ≫ 𝒰.f j = a.hom.left ≫ W.ι := by
  let W := (intersectionOpens (fun j ↦ (𝒰.f j).opensRange)).obj (.op s)
  let T : Over (Spec (.of K)) := Over.mk (W.ι ≫ base)
  let A := ((algΓ (.of K)).obj T).unop
  have (j : 𝒰.I₀) : IsAffine (𝒰.X j) := hU j
  have (j : 𝒰.I₀) : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  have hW : IsAffineOpen W := intersectionOpens_affine
    (fun j ↦ (𝒰.f j).opensRange) (fun j ↦ isAffineOpen_opensRange (𝒰.f j)) (.op s)
  have : IsAffine T.left := hW
  have : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app T) :=
    coordinates_unit_isIso (.of K) T
  let a : (algSpec (.of K)).obj (.op A) ≅ T :=
    (asIso ((algΓAlgSpecAdjunction (.of K)).unit.app T)).symm
  let φ := a.hom.left ≫ W.ι
  have hφ : φ ≫ base = ((algSpec (.of K)).obj (.op A)).hom := by
    have hw : a.hom.left ≫ (W.ι ≫ base) =
        ((algSpec (.of K)).obj (.op A)).hom := a.hom.w
    simpa only [φ, Category.assoc] using hw
  have hp (j : 𝒰.I₀) (hj : j ∈ s.val) : Set.range φ ⊆ Set.range (𝒰.f j) := by
    have hle : W ≤ (𝒰.f j).opensRange :=
      iInf_le_of_le j (iInf_le _ hj)
    rintro z ⟨t, rfl⟩
    exact hle (a.hom.left t).property
  let p (j : 𝒰.I₀) (hj : j ∈ s.val) :
      (algSpec (.of K)).obj (.op A) ⟶ Over.mk (𝒰.f j ≫ base) :=
    Over.homMk (IsOpenImmersion.lift (𝒰.f j) φ (hp j hj)) (by
      change IsOpenImmersion.lift (𝒰.f j) φ (hp j hj) ≫ (𝒰.f j ≫ base) = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hφ])
  refine ⟨a, rfl, p, ?_⟩
  intro j hj
  exact IsOpenImmersion.lift_fac (𝒰.f j) φ (hp j hj)

private theorem inverse_square {C : Type*} [Category C]
    {A B D E : C} (a : A ≅ B) (d : D ≅ E) (u : D ⟶ A) (v : E ⟶ B)
    (h : v ≫ a.inv = d.inv ≫ u) : u ≫ a.hom = d.hom ≫ v := by
  calc
    _ = d.hom ≫ (d.inv ≫ u) ≫ a.hom := by simp [Category.assoc]
    _ = d.hom ≫ (v ≫ a.inv) ≫ a.hom := by rw [← h]
    _ = _ := by simp [Category.assoc]

private theorem over_square_leg {S X : Scheme.{u}} {A B C D : Over S}
    (u : A ⟶ B) (a : B ⟶ C) (b : A ⟶ D) (v : D ⟶ C)
    (h : u ≫ a = b ≫ v) (i : C.left ⟶ X) (j : D.left ⟶ X)
    (hv : v.left ≫ i = j) : u.left ≫ a.left ≫ i = b.left ≫ j := by
  have hh : u.left ≫ a.left ≫ i = b.left ≫ v.left ≫ i := by
    have he := congrArg (fun q : A ⟶ C ↦ q.left ≫ i) h
    simpa only [Over.comp_left, Category.assoc] using he
  exact hh.trans (congrArg (fun q ↦ b.left ≫ q) hv)

/-- Finite intersections share their coordinate rings and natural chart lifts. -/
theorem intersection_coordinate_family {X : Scheme.{u}} {K : Type u}
    [CommRing K] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (𝒰 : X.OpenCover.{u})
    (hU : ∀ j, IsAffine (𝒰.X j)) :
    let I := {s : Finset 𝒰.I₀ // s.Nonempty}
    let W := intersectionOpens (fun j ↦ (𝒰.f j).opensRange)
    let E := W ⋙ X.restrictFunctor ⋙ Over.map base
    let F := intersectionCoordinates base (intersectionOpens (fun j ↦ (𝒰.f j).opensRange))
    ∃ a : ∀ s : I, (algSpec (.of K)).obj (.op (F.obj s)) ≅ E.obj (.op s),
      (∀ s, (a s).inv = (algΓAlgSpecAdjunction (.of K)).unit.app (E.obj (.op s))) ∧
      ∃ p : ∀ (s : I) (j : 𝒰.I₀) (_ : j ∈ s.val),
          (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk (𝒰.f j ≫ base),
        (∀ s j hj, (p s j hj).left ≫ 𝒰.f j =
          (a s).hom.left ≫ (W.obj (.op s)).ι) ∧
        ∀ (s t : I) (f : s ⟶ t) j (hj : j ∈ s.val),
          (algSpec (.of K)).map (F.map f).op ≫ p s j hj =
            p t j ((leOfHom f) hj) := by
  classical
  let I := {s : Finset 𝒰.I₀ // s.Nonempty}
  let W := intersectionOpens (fun j ↦ (𝒰.f j).opensRange)
  let E := W ⋙ X.restrictFunctor ⋙ Over.map base
  let F := intersectionCoordinates base (intersectionOpens (fun j ↦ (𝒰.f j).opensRange))
  have hh (s : I) :
      ∃ a : (algSpec (.of K)).obj (.op (F.obj s)) ≅ E.obj (.op s),
        a.inv = (algΓAlgSpecAdjunction (.of K)).unit.app (E.obj (.op s)) ∧
        ∃ p : ∀ j ∈ s.val,
            (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk (𝒰.f j ≫ base),
          ∀ j hj, (p j hj).left ≫ 𝒰.f j = a.hom.left ≫ (W.obj (.op s)).ι :=
    intersection_coordinate_lifts base 𝒰 hU s
  choose a ha p hp using hh
  refine ⟨a, ha, p, hp, ?_⟩
  intro s t f j hj
  have hu : E.map f.op ≫ (a s).inv = (a t).inv ≫
      (algSpec (.of K)).map (F.map f).op := by
    rw [ha s, ha t]
    exact (algΓAlgSpecAdjunction (.of K)).unit.naturality (E.map f.op)
  have hn := inverse_square (a s) (a t)
    ((algSpec (.of K)).map (F.map f).op) (E.map f.op) hu
  have hinc : (E.map f.op).left ≫ (W.obj (.op s)).ι = (W.obj (.op t)).ι := by
    change X.homOfLE (leOfHom (W.map f.op)) ≫ (W.obj (.op s)).ι = _
    exact Scheme.homOfLE_ι X _
  apply Over.OverMorphism.ext
  apply (cancel_mono (𝒰.f j)).mp
  simp only [Over.comp_left, Category.assoc]
  rw [hp s j hj, hp t j ((leOfHom f) hj)]
  exact over_square_leg ((algSpec (.of K)).map (F.map f).op) (a s).hom
    (a t).hom (E.map f.op) hn (W.obj (.op s)).ι (W.obj (.op t)).ι hinc

end FrobeniusSplitting
