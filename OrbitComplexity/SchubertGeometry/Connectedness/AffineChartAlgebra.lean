import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.NilpotentFibres
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.GeometricSourceIso
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import OrbitComplexity.FrobeniusSplitting.Normality.TensorCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.SectionRetention
import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import OrbitComplexity.SchubertGeometry.Connectedness.CellIntersection
import OrbitComplexity.GroupActions.Varieties.AffineTensorAction

/-!
# Algebra coordinates of an arbitrary affine scheme over a ring

-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

variable {R : Type u} [CommRing R]

@[instance_reducible]
private def bundledCoefficientAlgebra (S : CommRingCat.{u})
    (X : Over (Spec S)) [IsAffine X.left] : Algebra S Γ(X.left, ⊤) := by
  letI : X.left.Over (Spec S) := OverClass.fromOver X
  infer_instance

/-- The base algebra on global functions of an affine scheme over the base spectrum. -/
@[instance_reducible]
def coefficientAlgebra (X : Over (Spec (.of R))) [IsAffine X.left] :
    Algebra R Γ(X.left, ⊤) :=
  bundledCoefficientAlgebra (.of R) X

attribute [local instance] coefficientAlgebra

private def bundledCoefficientIso (S : CommRingCat.{u})
    (X : Over (Spec S)) [IsAffine X.left] :
    letI : Algebra S Γ(X.left, ⊤) := bundledCoefficientAlgebra S X
    (Spec (.of Γ(X.left, ⊤))).asOver (Spec S) ≅ X := by
  letI : X.left.Over (Spec S) := OverClass.fromOver X
  letI : Algebra S Γ(X.left, ⊤) := bundledCoefficientAlgebra S X
  exact (Over.isoMk X.left.isoSpec
    ((X.left.isoSpec.hom).asOver (Spec S)).w).symm

/-- The original affine counit as an isomorphism over the original base. -/
def coefficientIso (X : Over (Spec (.of R))) [IsAffine X.left] :
    (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of R)) ≅ X :=
  bundledCoefficientIso (.of R) X

/-- The relative affine counit has the original inverse-counit scheme map. -/
theorem coefficientIso_hom_left (X : Over (Spec (.of R))) [IsAffine X.left] :
    (coefficientIso X).hom.left = X.left.isoSpec.inv := rfl

/-- The inverse relative affine counit has the original counit scheme map. -/
theorem coefficientIso_inv_left (X : Over (Spec (.of R))) [IsAffine X.left] :
    (coefficientIso X).inv.left = X.left.isoSpec.hom := rfl

variable {A : Type u} [CommRing A] [Algebra R A]

private def coefficientChartMap (X : Over (Spec (.of R))) [IsAffine X.left]
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    (algSpec (.of R)).obj (Opposite.op (CommAlgCat.of R Γ(X.left, ⊤))) ⟶
      (algSpec (.of R)).obj (Opposite.op (CommAlgCat.of R A)) :=
  (coefficientIso X).hom ≫ f

/-- The specified relative chart map determines an algebra homomorphism on functions. -/
def chartAlgHom (X : Over (Spec (.of R))) [IsAffine X.left]
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) : A →ₐ[R] Γ(X.left, ⊤) := by
  letI : (algSpec (.of R)).Full := algSpec.instFull (R := .of R)
  exact ((algSpec (.of R)).preimage (coefficientChartMap X f)).unop.hom

/-- The relative spectrum map is the specified relative chart square. -/
theorem chartAlgHom_over_square (X : Over (Spec (.of R))) [IsAffine X.left]
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    GroupActions.algebraSpecMap (chartAlgHom X f) = (coefficientIso X).hom ≫ f := by
  let : (algSpec (.of R)).Full := algSpec.instFull (R := .of R)
  exact (algSpec (.of R)).map_preimage (coefficientChartMap X f)

/-- The algebra-coordinate map retains the original relative chart morphism. -/
theorem chartAlgHom_square (X : Over (Spec (.of R))) [IsAffine X.left]
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    Spec.map (CommRingCat.ofHom (chartAlgHom X f).toRingHom) =
      X.left.isoSpec.inv ≫ f.left := by
  have h := congrArg
    (fun g : (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of R)) ⟶
      (Spec (.of A)).asOver (Spec (.of R)) => g.left)
    (chartAlgHom_over_square X f)
  change Spec.map (CommRingCat.ofHom (chartAlgHom X f).toRingHom) =
    (coefficientIso X).hom.left ≫ f.left at h
  exact h.trans (congrArg (fun g : Spec (.of Γ(X.left, ⊤)) ⟶ X.left =>
    g ≫ f.left) (coefficientIso_hom_left X))

/-- Relative algebra coordinates and counit ring coordinates are the same map. -/
theorem chartAlgHom_eq (X : Over (Spec (.of R))) [IsAffine X.left]
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    CommRingCat.ofHom (chartAlgHom X f).toRingHom = closedChartCoordinates f.left := by
  apply Spec.map_injective
  exact (chartAlgHom_square X f).trans (closedChartCoordinates_square f.left).symm

/-- Nonemptiness of an affine scheme gives a nontrivial specified coordinate ring. -/
theorem coefficient_nontrivial (X : Over (Spec (.of R))) [IsAffine X.left]
    (hne : Nonempty X.left) : Nontrivial Γ(X.left, ⊤) :=
  PrimeSpectrum.nonempty_iff_nontrivial.mp
    ⟨X.left.isoSpec.hom (Classical.choice hne)⟩

/-- Connectedness of the specified affine coordinates transports to the original scheme. -/
theorem connected_of_coefficients (X : Over (Spec (.of R))) [IsAffine X.left]
    (h : ConnectedSpace (Spec (.of Γ(X.left, ⊤)))) : ConnectedSpace X.left :=
  (Scheme.homeoOfIso X.left.isoSpec).connectedSpace_iff.mpr h

/-- A spectrum factorization kills the kernel of its original coordinate map. -/
theorem zero_of_spec_factor {C D : Type u} [CommRing C] [CommRing D]
    (q : A →+* C) (l : A →+* D) (f : Spec (.of D) ⟶ Spec (.of C))
    (h : Spec.map (CommRingCat.ofHom l) =
      f ≫ Spec.map (CommRingCat.ofHom q))
    (a : A) (ha : q a = 0) : l a = 0 := by
  have he : CommRingCat.ofHom l =
      CommRingCat.ofHom q ≫ Spec.preimage f := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact h
  have hv := congrArg
    (fun g : CommRingCat.of A ⟶ CommRingCat.of D => g.hom a) he
  exact hv.trans (by change (Spec.preimage f).hom (q a) = 0; rw [ha, map_zero])

end SchubertGeometry.CellContraction


namespace SchubertGeometry

open CategoryTheory.Limits FrobeniusSplitting GroupActions Polynomial CellContraction
open scoped TensorProduct

universe u

private theorem with_witness {A : Type*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private theorem polynomial_baseChange_X (S A : Type u) [CommRing S] [CommRing A]
    [Algebra S A] :
    (polynomialTensorEquiv S A).symm Polynomial.X = (1 : A) ⊗ₜ[S] Polynomial.X := by
  apply (polynomialTensorEquiv S A).injective
  simp [polynomialTensorEquiv_tmul]

private def structural_chart_hom {S P : Type u} [CommRing S] [CommRing P]
    [Algebra S P] {Z : Scheme.{u}} (a : Z ⟶ Spec (.of S))
    (p : Z ⟶ Spec (.of P))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S P)) = a) :
    let _ : Algebra S Γ(Z, ⊤) :=
      (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    P →ₐ[S] Γ(Z, ⊤) := by
  intro inst
  refine { (closedChartCoordinates p).hom with commutes' := ?_ }
  intro s
  have hnat := congrArg (fun f : CommRingCat.of S ⟶ Γ(Spec (.of P), ⊤) => f s)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap S P)))
  have hmap : (Spec.map (CommRingCat.ofHom (algebraMap S P))).appTop ≫ p.appTop =
      a.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg (fun f : Z ⟶ Spec (.of S) => f.appTop) hp
  change p.appTop ((Scheme.ΓSpecIso (.of P)).inv (algebraMap S P s)) =
    a.appTop ((Scheme.ΓSpecIso (.of S)).inv s)
  exact (congrArg p.appTop hnat).trans
    (congrArg (fun f : Γ(Spec (.of S), ⊤) ⟶ Γ(Z, ⊤) =>
      f ((Scheme.ΓSpecIso (.of S)).inv s)) hmap)

private theorem structural_spec_map {A : Type u} [CommRing A]
    {W : Scheme.{u}} [IsAffine W] (b : W ⟶ Spec (.of A)) :
    let _ : Algebra A Γ(W, ⊤) :=
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
    W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(W, ⊤))) = b := by
  intro inst
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap A Γ(W, ⊤))) =
      W.isoSpec.inv ≫ b := closedChartCoordinates_square b
  exact (congrArg (fun f => W.isoSpec.hom ≫ f) hbase).trans
    (W.isoSpec.hom_inv_id_assoc b)

private theorem tensor_nilpotent_gc {A P : Type u} [CommRing A] [CommRing P]
    [Algebra A P] (c : A[X] →ₐ[A] P) (hc : Function.Surjective c)
    (N : ℕ) (hN : 0 < N) (hn : (c Polynomial.X) ^ N = 0)
    (σ : Spec (.of A) ⟶ Spec (.of P))
    (hσ : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap A P)) = 𝟙 _) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap A P))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap A P))
  let f := Spec.map (CommRingCat.ofHom c.toRingHom)
  have hf : f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* A[X])) = b := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact c.commutes a
  let d : Over.mk b ⟶ Over.mk
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* A[X]))) := Over.homMk f hf
  let : IsClosedImmersion d.left := IsClosedImmersion.spec_of_surjective _ hc
  have he : f.appTop ((Scheme.ΓSpecIso (.of A[X])).inv Polynomial.X) =
      (Scheme.ΓSpecIso (.of P)).inv (c Polynomial.X) := by
    have H := congrArg (fun q : CommRingCat.of A[X] ⟶ Γ(Spec (.of P), ⊤) => q Polynomial.X)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c.toRingHom))
    exact H.symm
  have hnil : (f.appTop ((Scheme.ΓSpecIso (.of A[X])).inv Polynomial.X)) ^ N = 0 := by
    rw [he, ← map_pow, hn, map_zero]
  exact geomConnected_of_nilpotent_chart b d ⟨N, hN, hnil⟩ ⟨σ, hσ⟩

private theorem affine_tensor_gc {S A : Type u} [CommRing S] [CommRing A]
    [Algebra S A] {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W]
    (a : Z ⟶ Spec (.of S)) (b : W ⟶ Spec (.of A)) (q : W ⟶ Z)
    (h : IsPullback q b a (Spec.map (CommRingCat.ofHom (algebraMap S A))))
    (p : Z ⟶ Spec (.of S[X])) [IsClosedImmersion p]
    (hp : p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])) = a)
    (N : ℕ) (hN : 0 < N) :
    let _ : Algebra S Γ(Z, ⊤) :=
      (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : A) ⊗ₜ[S]
      ((p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) ^ N) = 0 →
    (∃ σ : Spec (.of A) ⟶ W, σ ≫ b = 𝟙 _) → GeometricallyConnected b := by
  intro inst hn hsection
  let c : S[X] →ₐ[S] Γ(Z, ⊤) := structural_chart_hom a p hp
  have hc : Function.Surjective c := closedChartCoordinates_surjective p
  have hX : c Polynomial.X =
      p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X) := by
    rfl
  let _ : Algebra A Γ(W, ⊤) :=
    (b.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  refine with_witness (exists_affine_scalar_coordinates a b q h) ?_
  intro e _
  let cA : A[X] →ₐ[A] A ⊗[S] Γ(Z, ⊤) :=
    (Algebra.TensorProduct.map (AlgHom.id A A) c).comp
      (polynomialTensorEquiv S A).symm.toAlgHom
  have hcA : Function.Surjective cA :=
    (Algebra.TensorProduct.map_surjective (f := AlgHom.id A A) (g := c)
      Function.surjective_id hc).comp (polynomialTensorEquiv S A).symm.surjective
  have hcAX : cA Polynomial.X = (1 : A) ⊗ₜ[S] c Polynomial.X := by
    simp only [cA, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, polynomial_baseChange_X,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hnA : (cA Polynomial.X) ^ N = 0 := by
    rw [hcAX, Algebra.TensorProduct.tmul_pow, one_pow, hX]
    exact hn
  let d : A[X] →ₐ[A] Γ(W, ⊤) := e.toAlgHom.comp cA
  have hd : Function.Surjective d := e.surjective.comp hcA
  have hdn : (d Polynomial.X) ^ N = 0 := by
    change (e (cA Polynomial.X)) ^ N = 0
    rw [← map_pow, hnA, map_zero]
  obtain ⟨σ, hσ⟩ := hsection
  have hmap : W.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A Γ(W, ⊤))) = b := structural_spec_map b
  have hσ' : (σ ≫ W.isoSpec.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A Γ(W, ⊤))) = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (fun f => σ ≫ f) hmap).trans hσ)
  let : GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap A Γ(W, ⊤)))) :=
    tensor_nilpotent_gc d hd N hN hdn (σ ≫ W.isoSpec.hom) hσ'
  have hE := geomConnected_comp_iso W.isoSpec
    (Spec.map (CommRingCat.ofHom (algebraMap A Γ(W, ⊤))))
  exact hmap ▸ hE

private theorem affine_tensor_empty {S A : Type u} [CommRing S] [CommRing A]
    [Algebra S A] {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W]
    (a : Z ⟶ Spec (.of S)) (b : W ⟶ Spec (.of A)) (q : W ⟶ Z)
    (h : IsPullback q b a (Spec.map (CommRingCat.ofHom (algebraMap S A)))) :
    let _ : Algebra S Γ(Z, ⊤) :=
      (a.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : A) ⊗ₜ[S] (1 : Γ(Z, ⊤)) = 0 → IsEmpty W := by
  intro inst he
  let _ : Algebra A Γ(W, ⊤) :=
    (b.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  refine with_witness (exists_affine_scalar_coordinates a b q h) ?_
  intro e _
  have htensor : (1 : A ⊗[S] Γ(Z, ⊤)) = 0 := by
    simpa only [Algebra.TensorProduct.one_def] using he
  have hone : (1 : Γ(W, ⊤)) = 0 := by
    simpa only [map_one, map_zero] using congrArg e htensor
  let : Subsingleton Γ(W, ⊤) := subsingleton_of_zero_eq_one hone.symm
  let : IsEmpty (Spec (.of Γ(W, ⊤))) := inferInstanceAs (IsEmpty (PrimeSpectrum Γ(W, ⊤)))
  exact ⟨fun x => isEmptyElim (W.isoSpec.hom x)⟩

private theorem first_open_isIso {I Z W IA : Scheme.{u}}
    (q : Z ⟶ I) (q' : W ⟶ I) [IsOpenImmersion q]
    (qI : IA ⟶ I) (hc : ∀ x : I, x ∈ Set.range q ∨ x ∈ Set.range q')
    (he : IsEmpty (pullback q' qI : Scheme.{u})) :
    IsIso (pullback.snd q qI) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  rcases hc (qI x) with ⟨z, hz⟩ | ⟨w, hw⟩
  · obtain ⟨t, _, ht⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    exact ⟨t, ht⟩
  · obtain ⟨t, _, _⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
    exact (he.false t).elim

private theorem scalar_chart_affine {S A : Type u} [CommRing S] [CommRing A]
    [Algebra S A] {Z W : Scheme.{u}} [IsAffine Z]
    (a : Z ⟶ Spec (.of S)) (b : W ⟶ Spec (.of A)) (q : W ⟶ Z)
    (h : IsPullback q b a (Spec.map (CommRingCat.ofHom (algebraMap S A)))) :
    IsAffine W := by
  let : IsAffineHom b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h inferInstance
  exact isAffine_of_isAffineHom b

private theorem nilpotent_section_zero {A : Type u} [CommRing A] [IsDomain A]
    {W : Scheme.{u}} (σ : Spec (.of A) ⟶ W) (x : Γ(W, ⊤))
    (N : ℕ) (hn : x ^ N = 0) : σ.appTop x = 0 := by
  have hpow : (((Scheme.ΓSpecIso (.of A)).hom (σ.appTop x)) ^ N) = 0 := by
    rw [← map_pow, ← map_pow, hn, map_zero, map_zero]
  have hz : (Scheme.ΓSpecIso (.of A)).hom (σ.appTop x) = 0 :=
    isNilpotent_iff_eq_zero.mp ⟨N, hpow⟩
  calc
    σ.appTop x = (Scheme.ΓSpecIso (.of A)).inv
        ((Scheme.ΓSpecIso (.of A)).hom (σ.appTop x)) :=
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of A)) (σ.appTop x)).symm
    _ = 0 := by rw [hz, map_zero]

/-- Nilpotent affine chart relations give connected geometric fibres of a closed cover. -/
theorem scalar_cover_gc {S A : Type u} [CommRing S] [CommRing A] [IsDomain A]
    [Algebra S A] {I IA Z W : Scheme.{u}} [IsAffine Z] [IsAffine W]
    (b : I ⟶ Spec (.of S)) (bA : IA ⟶ Spec (.of A)) (qI : IA ⟶ I)
    (hI : IsPullback qI bA b (Spec.map (CommRingCat.ofHom (algebraMap S A))))
    (q : Z ⟶ I) (q' : W ⟶ I) [IsOpenImmersion q]
    (p : Z ⟶ Spec (.of S[X])) [IsClosedImmersion p]
    (hp : p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])) = q ≫ b)
    (hc : ∀ x : I, x ∈ Set.range q ∨ x ∈ Set.range q')
    (N : ℕ) (hN : 0 < N) :
    let _ : Algebra S Γ(Z, ⊤) :=
      ((q ≫ b).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let _ : Algebra S Γ(W, ⊤) :=
      ((q' ≫ b).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    (1 : A) ⊗ₜ[S]
      ((p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X)) ^ N) = 0 →
    (1 : A) ⊗ₜ[S] (1 : Γ(W, ⊤)) = 0 →
    ∀ (σ : Spec (.of A) ⟶ IA), σ ≫ bA = 𝟙 _ →
    ∃ E : (pullback q qI : Scheme.{u}) ≅ IA,
      E.hom = pullback.snd q qI ∧
      ((pullback.fst q qI).appTop
        (p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X))) ^ N = 0 ∧
      (σ ≫ E.inv).appTop ((pullback.fst q qI).appTop
        (p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X))) = 0 ∧
      GeometricallyConnected bA := by
  intro instZ instW hn he σ hσ
  let qA := pullback.snd q qI
  let pA := pullback.fst q qI
  let qA' := pullback.snd q' qI
  let pA' := pullback.fst q' qI
  have hZ : IsPullback pA (qA ≫ bA) (q ≫ b)
      (Spec.map (CommRingCat.ofHom (algebraMap S A))) :=
    (IsPullback.of_hasPullback q qI).paste_vert hI
  have hW : IsPullback pA' (qA' ≫ bA) (q' ≫ b)
      (Spec.map (CommRingCat.ofHom (algebraMap S A))) :=
    (IsPullback.of_hasPullback q' qI).paste_vert hI
  let : IsAffine (pullback q qI : Scheme.{u}) := scalar_chart_affine _ _ _ hZ
  let : IsAffine (pullback q' qI : Scheme.{u}) := scalar_chart_affine _ _ _ hW
  have he' : IsEmpty (pullback q' qI : Scheme.{u}) := affine_tensor_empty _ _ _ hW he
  let : IsIso qA := first_open_isIso q q' qI hc he'
  have hσA : (σ ≫ (asIso qA).inv) ≫ (qA ≫ bA) = 𝟙 _ := by
    rw [Category.assoc]
    exact (congrArg (fun k => σ ≫ k) ((asIso qA).inv_hom_id_assoc bA)).trans hσ
  let : GeometricallyConnected (qA ≫ bA) :=
    affine_tensor_gc (q ≫ b) (qA ≫ bA) pA hZ p hp N hN hn
      ⟨σ ≫ (asIso qA).inv, hσA⟩
  have hgc := geomConnected_comp_iso (asIso qA).symm (qA ≫ bA)
  have hgc' : GeometricallyConnected bA :=
    ((asIso qA).inv_hom_id_assoc bA) ▸ hgc
  let _ : Algebra A Γ(pullback q qI, ⊤) :=
    ((qA ≫ bA).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  refine with_witness (exists_affine_scalar_coordinates (q ≫ b) (qA ≫ bA) pA hZ) ?_
  intro e hcoord
  have hpow : (pA.appTop
      (p.appTop ((Scheme.ΓSpecIso (.of S[X])).inv Polynomial.X))) ^ N = 0 := by
    have H := congrArg e hn
    rw [hcoord.2.1, map_pow, map_zero] at H
    exact H
  exact ⟨asIso qA, rfl, hpow,
    nilpotent_section_zero (σ ≫ (asIso qA).inv) _ N hpow, hgc'⟩

end SchubertGeometry
