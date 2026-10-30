import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius

/-! # Global monomial generators on the projective line -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

private def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private abbrev line (C : Type u) [CommRing C] := projectiveScheme C (ULift.{u} (Fin 2))
private abbrev affine (C : Type u) [CommRing C] := Spec (.of (Polynomial C))
private abbrev overlap (C : Type u) [CommRing C] := Spec (.of (LaurentPolynomial C))
private abbrev chart (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  projectiveLinePolynomialChart C j

private def leftMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

private def rightMap (C : Type u) [CommRing C] : overlap C ⟶ affine C :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

private def overlapMap (C : Type u) [CommRing C] : overlap C ⟶ line C :=
  leftMap C ≫ chart C ⟨0⟩

private def chartModule (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    (line C).Modules :=
  (Scheme.Modules.pushforward (chart C j)).obj (SheafOfModules.unit (affine C).ringCatSheaf)

private def transitionSection (C : Type u) [CommRing C] (d : ℕ) : Γ(overlap C, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv (LaurentPolynomial.T (d : ℤ))

private abbrev chartCounit (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso (chart C j)).app
    (structureModule (affine C))).hom

private theorem unit_top_ext {X : Scheme.{u}} {M : X.Modules}
    (f g : structureModule X ⟶ M)
    (h : (f.val.app (.op ⊤)).hom (1 : Γ(X, ⊤)) =
      (g.val.app (.op ⊤)).hom (1 : Γ(X, ⊤))) : f = g := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hf := PresheafOfModules.sections_property (M.unitHomEquiv f) U.unop.leTop.op
  have hg := PresheafOfModules.sections_property (M.unitHomEquiv g) U.unop.leTop.op
  rw [← hf, ← hg]
  exact congrArg (M.val.map U.unop.leTop.op) h

private def chartSection (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2))
    (f : Polynomial C) : structureModule (line C) ⟶ chartModule C j :=
  SheafOfModules.unitToPushforwardObjUnit (chart C j).toRingCatSheafHom ≫
    (Scheme.Modules.pushforward (chart C j)).map
      (Scheme.Modules.globalSectionsSmul _ ((Scheme.ΓSpecIso (.of (Polynomial C))).inv f))

private theorem module_comp_apply {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : X.Opens) (s : M.val.obj (.op U)) :
    ((f ≫ g).val.app (.op U)).hom s =
      (g.val.app (.op U)).hom ((f.val.app (.op U)).hom s) := rfl

private theorem chartSection_top (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2))
    (f : Polynomial C) :
    ((chartSection C j f).val.app (.op ⊤)).hom (1 : Γ(line C, ⊤)) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv f := by
  change (affine C).presheaf.map (𝟙 (.op ⊤))
      ((Scheme.ΓSpecIso (.of (Polynomial C))).inv f) * (chart C j).appTop 1 = _
  simp

private theorem leftRestriction_top (C : Type u) [CommRing C] (s : Γ(affine C, ⊤)) :
    ((leftRestriction C).val.app (.op ⊤)).hom s = (leftMap C).appTop s := rfl

private theorem rightRestriction_top (C : Type u) [CommRing C] (s : Γ(affine C, ⊤)) :
    ((rightRestriction C).val.app (.op ⊤)).hom s = (rightMap C).appTop s := by
  change (overlap C).presheaf.map (𝟙 (.op ⊤)) ((rightMap C).appTop s) = _
  simp

private theorem twistedRestriction_top (C : Type u) [CommRing C] (d : ℕ)
    (s : Γ(affine C, ⊤)) :
    ((twistedRestriction C d).val.app (.op ⊤)).hom s =
      transitionSection C d * (rightMap C).appTop s := by
  erw [module_comp_apply (rightRestriction C)
    ((Scheme.Modules.pushforward (overlapMap C)).map
      (Scheme.Modules.globalSectionsSmul _ (transitionSection C d))) ⊤ s,
    rightRestriction_top C s]
  change (overlap C).presheaf.map (𝟙 (.op ⊤)) (transitionSection C d) *
    (rightMap C).appTop s = _
  simp

private theorem monomial_values (C : Type u) [CommRing C] (d k : ℕ) (hk : k ≤ d) :
    (leftMap C).appTop ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ k)) =
      transitionSection C d * (rightMap C).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (d - k))) := by
  have h₀ := congrArg (fun f => f (Polynomial.X ^ k))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial C →+* LaurentPolynomial C)))
  have h₁ := congrArg (fun f => f (Polynomial.X ^ (d - k)))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial C ≃ₐ[C] LaurentPolynomial C).toRingHom.comp
        Polynomial.toLaurent)))
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv
    (Polynomial.toLaurent (Polynomial.X ^ k)) =
      (leftMap C).appTop ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ k)) at h₀
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv
    (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X ^ (d - k)))) =
      (rightMap C).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (d - k))) at h₁
  rw [← h₀, ← h₁]
  have he : Polynomial.toLaurent (Polynomial.X ^ k : Polynomial C) =
      LaurentPolynomial.T (d : ℤ) *
        LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X ^ (d - k))) := by
    simp only [Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_T]
    rw [← LaurentPolynomial.T_add]
    congr 1
    omega
  exact (congrArg ((Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv) he).trans
    (map_mul (Scheme.ΓSpecIso (.of (LaurentPolynomial C))).inv.hom _ _)

private theorem monomial_matching (C : Type u) [CommRing C] (d k : ℕ) (hk : k ≤ d) :
    chartSection C ⟨0⟩ (Polynomial.X ^ k) ≫ leftRestriction C =
      chartSection C ⟨1⟩ (Polynomial.X ^ (d - k)) ≫ twistedRestriction C d := by
  apply unit_top_ext
  have hleft :
      ((chartSection C ⟨0⟩ (Polynomial.X ^ k) ≫ leftRestriction C).val.app (.op ⊤)).hom
          (1 : Γ(line C, ⊤)) =
        (leftMap C).appTop
          ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ k)) :=
    (module_comp_apply (chartSection C ⟨0⟩ (Polynomial.X ^ k)) (leftRestriction C)
      ⊤ (1 : Γ(line C, ⊤))).trans
      ((congrArg (fun s : Γ(affine C, ⊤) =>
          ((leftRestriction C).val.app (.op ⊤)).hom s)
        (chartSection_top C ⟨0⟩ (Polynomial.X ^ k))).trans (leftRestriction_top C _))
  have hright :
      ((chartSection C ⟨1⟩ (Polynomial.X ^ (d - k)) ≫ twistedRestriction C d).val.app
          (.op ⊤)).hom (1 : Γ(line C, ⊤)) =
        transitionSection C d * (rightMap C).appTop
          ((Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (d - k))) :=
    (module_comp_apply (chartSection C ⟨1⟩ (Polynomial.X ^ (d - k)))
      (twistedRestriction C d) ⊤ (1 : Γ(line C, ⊤))).trans
      ((congrArg (fun s : Γ(affine C, ⊤) =>
          ((twistedRestriction C d).val.app (.op ⊤)).hom s)
        (chartSection_top C ⟨1⟩ (Polynomial.X ^ (d - k)))).trans
          (twistedRestriction_top C d _))
  exact hleft.trans ((monomial_values C d k hk).trans hright.symm)

private def monomialSection (C : Type u) [CommRing C] (d k : ℕ) (hk : k ≤ d) :
    structureModule (line C) ⟶ projectiveTransitionModule C d :=
  pullback.lift (chartSection C ⟨0⟩ (Polynomial.X ^ k))
    (chartSection C ⟨1⟩ (Polynomial.X ^ (d - k))) (monomial_matching C d k hk)

private def sectionToFrobenius (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M : X.Modules) (s : M.sections) :
    (FrobeniusSplitting.frobeniusRestriction C p base M).sections where
  val U := s.val U
  property f := s.property f

/-- Global residue monomials define the evaluation morphism into the Frobenius-restricted
transition module on the projective line. -/
def projectiveFrobeniusEval (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] :
    (SheafOfModules.free (R := (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf)
        (ULift.{u} (Fin p)) : (projectiveScheme C (ULift.{u} (Fin 2))).Modules) ⟶
      FrobeniusSplitting.frobeniusRestriction C p
        (projectiveToSpec C (ULift.{u} (Fin 2))) (projectiveTransitionModule C (p - 1)) :=
  (SheafOfModules.freeHomEquiv _).symm fun k : ULift.{u} (Fin p) =>
    sectionToFrobenius C p (projectiveToSpec C (ULift.{u} (Fin 2)))
      (projectiveTransitionModule C (p - 1))
      ((projectiveTransitionModule C (p - 1)).unitHomEquiv
        (monomialSection C (p - 1) k.down (Nat.le_sub_one_of_lt k.down.isLt)))

private theorem chartSection_restrict_top (C : Type u) [CommRing C]
    (j : ULift.{u} (Fin 2)) (f : Polynomial C) :
    ((chartCounit C j).val.app (.op ⊤)).hom
      (((chartSection C j f).val.app (.op (chart C j ''ᵁ ⊤))).hom
        (1 : Γ(line C, chart C j ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv f := by
  change (affine C).presheaf.map _
    ((affine C).presheaf.map _ ((Scheme.ΓSpecIso (.of (Polynomial C))).inv f) *
      (chart C j).app (chart C j ''ᵁ ⊤) 1) = _
  simp only [map_one, mul_one]
  rw [← Functor.map_comp_apply]
  simp

private theorem monomial_left_value (C : Type u) [CommRing C]
    (d k : ℕ) (hk : k ≤ d) :
    ((leftChartMap C d).val.app (.op ⊤)).hom
      (((monomialSection C d k hk).val.app (.op (chart C ⟨0⟩ ''ᵁ ⊤))).hom
        (1 : Γ(line C, chart C ⟨0⟩ ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ k) := by
  change ((chartCounit C ⟨0⟩).val.app (.op ⊤)).hom
      (((pullback.fst (leftRestriction C) (twistedRestriction C d)).val.app
        (.op (chart C ⟨0⟩ ''ᵁ ⊤))).hom
        (((monomialSection C d k hk).val.app (.op (chart C ⟨0⟩ ''ᵁ ⊤))).hom
          (1 : Γ(line C, chart C ⟨0⟩ ''ᵁ ⊤)))) = _
  erw [← module_comp_apply (monomialSection C d k hk)
    (pullback.fst (leftRestriction C) (twistedRestriction C d))]
  unfold monomialSection
  erw [pullback.lift_fst]
  exact chartSection_restrict_top C ⟨0⟩ (Polynomial.X ^ k)

private theorem monomial_right_value (C : Type u) [CommRing C]
    (d k : ℕ) (hk : k ≤ d) :
    ((rightChartMap C d).val.app (.op ⊤)).hom
      (((monomialSection C d k hk).val.app (.op (chart C ⟨1⟩ ''ᵁ ⊤))).hom
        (1 : Γ(line C, chart C ⟨1⟩ ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (d - k)) := by
  change ((chartCounit C ⟨1⟩).val.app (.op ⊤)).hom
      (((pullback.snd (leftRestriction C) (twistedRestriction C d)).val.app
        (.op (chart C ⟨1⟩ ''ᵁ ⊤))).hom
        (((monomialSection C d k hk).val.app (.op (chart C ⟨1⟩ ''ᵁ ⊤))).hom
          (1 : Γ(line C, chart C ⟨1⟩ ''ᵁ ⊤)))) = _
  erw [← module_comp_apply (monomialSection C d k hk)
    (pullback.snd (leftRestriction C) (twistedRestriction C d))]
  unfold monomialSection
  erw [pullback.lift_snd]
  exact chartSection_restrict_top C ⟨1⟩ (Polynomial.X ^ (d - k))

private def evaluationSection (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (k : ULift.{u} (Fin p)) :
    (FrobeniusSplitting.frobeniusRestriction C p
      (projectiveToSpec C (ULift.{u} (Fin 2)))
      (projectiveTransitionModule C (p - 1))).sections :=
  SheafOfModules.freeHomEquiv _ (projectiveFrobeniusEval C p) k

private theorem evaluation_left_value (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (k : ULift.{u} (Fin p)) :
    ((leftChartMap C (p - 1)).val.app (.op ⊤)).hom
      ((evaluationSection C p k).val (.op (chart C ⟨0⟩ ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (k.down : ℕ)) := by
  dsimp only [evaluationSection, projectiveFrobeniusEval]
  rw [Equiv.apply_symm_apply]
  exact monomial_left_value C (p - 1) k.down (Nat.le_sub_one_of_lt k.down.isLt)

private theorem evaluation_right_value (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (k : ULift.{u} (Fin p)) :
    ((rightChartMap C (p - 1)).val.app (.op ⊤)).hom
      ((evaluationSection C p k).val (.op (chart C ⟨1⟩ ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv
        (Polynomial.X ^ (p - 1 - (k.down : ℕ))) := by
  dsimp only [evaluationSection, projectiveFrobeniusEval]
  rw [Equiv.apply_symm_apply]
  exact monomial_right_value C (p - 1) k.down (Nat.le_sub_one_of_lt k.down.isLt)

/-- The Frobenius evaluation generators have residue-monomial coordinates
on the two polynomial charts. -/
theorem projectiveEval_generators (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (k : ULift.{u} (Fin p)) :
    (((projectiveTransitionChart C (p - 1) ⟨0⟩).hom.val.app (.op ⊤)).hom
      ((SheafOfModules.freeHomEquiv
        (FrobeniusSplitting.frobeniusRestriction C p
          (projectiveToSpec C (ULift.{u} (Fin 2)))
          (projectiveTransitionModule C (p - 1)))
        (projectiveFrobeniusEval C p) k).val
          (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (k.down : ℕ))) ∧
    (((projectiveTransitionChart C (p - 1) ⟨1⟩).hom.val.app (.op ⊤)).hom
      ((SheafOfModules.freeHomEquiv
        (FrobeniusSplitting.frobeniusRestriction C p
          (projectiveToSpec C (ULift.{u} (Fin 2)))
          (projectiveTransitionModule C (p - 1)))
        (projectiveFrobeniusEval C p) k).val
          (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv
        (Polynomial.X ^ (p - 1 - (k.down : ℕ)))) := by
  exact ⟨evaluation_left_value C p k, evaluation_right_value C p k⟩

end SchubertGeometry.ProjectiveLine
