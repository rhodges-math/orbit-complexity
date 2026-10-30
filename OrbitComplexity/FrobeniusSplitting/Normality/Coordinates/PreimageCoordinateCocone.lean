import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.IntersectionCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones

/-! # Canonical chart lifts on the retained open diagram -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem range_in_open {A X : Scheme.{u}} (f : A ⟶ X)
    (B O : X.Opens) (e : A ⟶ B.toScheme) (h : f = e ≫ B.ι) (hle : B ≤ O) :
    Set.range f ⊆ Set.range O.ι := by
  rintro y ⟨x, rfl⟩
  rw [h, Scheme.Hom.comp_apply, Scheme.Opens.range_ι]
  exact hle (e x).property

private theorem cocone_lifts {K : Type u} [CommRing K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) {I : Type u} (O : I → X.Opens)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj X)
    (hb : ∀ s, b.app (.op s) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hrange : ∀ s j (_hj : j ∈ s.val), Set.range (b.app (.op s)) ⊆ Set.range (O j).ι) :
    ∃ p : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk ((O j).ι ≫ base),
      (∀ s j hj, (p s j hj).left ≫ (O j).ι = b.app (.op s)) ∧
      (∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
        (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj)) ∧
      ∀ s j hj k hk, p s j hj ≫ Over.homMk (V := Over.mk base) (O j).ι rfl =
        p s k hk ≫ Over.homMk (V := Over.mk base) (O k).ι rfl := by
  let p (s : {s : Finset I // s.Nonempty}) (j : I) (hj : j ∈ s.val) :
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk ((O j).ι ≫ base) :=
    Over.homMk (IsOpenImmersion.lift (O j).ι (b.app (.op s)) (hrange s j hj)) (by
      change IsOpenImmersion.lift (O j).ι (b.app (.op s)) (hrange s j hj) ≫
        ((O j).ι ≫ base) = Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s)))
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hb s])
  have hp (s : {s : Finset I // s.Nonempty}) (j : I) (hj : j ∈ s.val) :
      (p s j hj).left ≫ (O j).ι = b.app (.op s) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨p, hp, ?_, ?_⟩
  · intro s t f j hj
    apply Over.OverMorphism.ext
    apply (cancel_mono (O j).ι).mp
    change ((algSpec (.of K)).map (F.map f).op).left ≫ (p s j hj).left ≫ (O j).ι = _
    rw [hp s j hj, hp t j ((leOfHom f) hj)]
    exact (b.naturality f.op).trans (Category.comp_id (b.app (.op t)))
  · intro s j hj k hk
    apply Over.OverMorphism.ext
    exact (hp s j hj).trans (hp s k hk).symm


private theorem standard_coordinate_cocone {K : Type u} [CommRing K] {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) {I : Type u} (O : I → X.Opens)
    (hO : ∀ j, IsAffineOpen (O j)) (hcover : (⨆ j, O j) = ⊤) :
    let V := intersectionOpens O
    let E := V ⋙ X.restrictFunctor ⋙ Over.map base
    let F := (E ⋙ algΓ (.of K)).unop
    ∃ (hE : ∀ s, IsAffine (E.obj s).left)
      (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
        (Functor.const _).obj X),
      Nonempty (IsColimit (Cocone.mk X b)) ∧
      (∀ s, b.app (.op s) ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s)))) ∧
      (∀ s, b.app s =
        (by letI := hE; exact ((coordinateDiagramIso (.of K) E).inv.app s).left) ≫
          (V.obj s).ι) ∧
      ∃ p : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val),
          (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk ((O j).ι ≫ base),
        (∀ s j hj, (p s j hj).left ≫ (O j).ι = b.app (.op s)) ∧
        (∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
          (algSpec (.of K)).map (F.map f).op ≫ p s j hj =
            p t j ((leOfHom f) hj)) ∧
        ∀ s j hj k hk, p s j hj ≫ Over.homMk (V := Over.mk base) (O j).ι rfl =
          p s k hk ≫ Over.homMk (V := Over.mk base) (O k).ι rfl := by
  let B := intersectionOpens O
  let E := B ⋙ X.restrictFunctor ⋙ Over.map base
  let F := (E ⋙ algΓ (.of K)).unop
  have hE (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj s).left :=
    intersectionOpens_affine O hO s
  let (s : {s : Finset I // s.Nonempty}ᵒᵖ) : IsAffine (E.obj s).left := hE s
  let cO := intersectionCoordinateCocone base O hO
  let c : Cocone (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) :=
    (Over.forget (Spec (.of K))).mapCocone cO
  have hc : IsColimit c :=
    isColimitOfPreserves (Over.forget (Spec (.of K))) (coordinateCoconeIsColimit base O hO hcover)
  have hb (s : {s : Finset I // s.Nonempty}) : c.ι.app (.op s) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))) := (cO.ι.app (.op s)).w
  have hleg (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
      c.ι.app s = ((coordinateDiagramIso (.of K) E).inv.app s).left ≫ (B.obj s).ι := rfl
  have hrange (s : {s : Finset I // s.Nonempty}) (j : I) (hj : j ∈ s.val) :
      Set.range (c.ι.app (.op s)) ⊆ Set.range (O j).ι := by
    let e : Spec (.of (F.obj s)) ⟶ (B.obj (.op s)).toScheme :=
      ((coordinateDiagramIso (.of K) E).inv.app (.op s)).left
    exact range_in_open (c.ι.app (.op s)) (B.obj (.op s)) (O j) e (hleg (.op s))
      (iInf_le_of_le j (iInf_le _ hj))
  obtain ⟨p, hp, hpn, hcommon⟩ := cocone_lifts base O F c.ι hb hrange
  exact ⟨hE, c.ι, ⟨hc⟩, hb, hleg, p, hp, hpn, hcommon⟩

/-- A retained intersection diagram has its coordinate colimit and natural
lifts to every labeled open, with all canonical leg equations. -/
theorem open_diagram_coordinate_cocone {K : Type u} [CommRing K] {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) {I : Type u} (O : I → X.Opens)
    (hO : ∀ j, IsAffineOpen (O j)) (hcover : (⨆ j, O j) = ⊤)
    (V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ X.Opens)
    (hV : V = intersectionOpens O) :
    let E := V ⋙ X.restrictFunctor ⋙ Over.map base
    let F := (E ⋙ algΓ (.of K)).unop
    ∃ (hE : ∀ s, IsAffine (E.obj s).left)
      (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
        (Functor.const _).obj X),
      Nonempty (IsColimit (Cocone.mk X b)) ∧
      (∀ s, b.app (.op s) ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s)))) ∧
      (∀ s, b.app s =
        (by letI := hE; exact ((coordinateDiagramIso (.of K) E).inv.app s).left) ≫
          (V.obj s).ι) ∧
      ∃ p : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val),
          (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk ((O j).ι ≫ base),
        (∀ s j hj, (p s j hj).left ≫ (O j).ι = b.app (.op s)) ∧
        (∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
          (algSpec (.of K)).map (F.map f).op ≫ p s j hj =
            p t j ((leOfHom f) hj)) ∧
        ∀ s j hj k hk, p s j hj ≫ Over.homMk (V := Over.mk base) (O j).ι rfl =
          p s k hk ≫ Over.homMk (V := Over.mk base) (O k).ι rfl := by
  subst V
  exact standard_coordinate_cocone base O hO hcover

end FrobeniusSplitting
