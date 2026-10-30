import OrbitComplexity.GroupActions.Rosenlicht.InvariantPullback
import OrbitComplexity.GroupActions.Rosenlicht.OpenInvariants

/-!
# Function fields of orbit quotients

The invariant-field model and an equivariant open immersion identify the quotient function
field with invariant rational functions. The factorization through the invariant morphism
makes this identification equal to pullback.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X Z : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Z.toOver]
variable [IrreducibleSpace X.scheme] [IrreducibleSpace Z.scheme]
variable (V : (invariantModel H X).scheme.Opens) [Nonempty V]
variable (i : Z.toOver ⟶ X.toOver) [IsModHom H.toOver i]
variable [IsOpenImmersion i.left] [IsDominant i.left]

/-- Restriction to a nonempty open of the invariant model identifies its function
field with the invariant field of an equivariant open subvariety. -/
def invariantOpenFieldEquiv :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : Z.scheme.Over (Spec (.of K)) := ⟨Z.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : IsIntegral Z.scheme := isIntegral_of_irreducibleSpace_of_isReduced Z.scheme
    letI : (invariantModel H X).scheme.Over (Spec (.of K)) :=
      ⟨(invariantModel H X).toSpec⟩
    letI : ((invariantModel H X).openSubvariety V).scheme.Over (Spec (.of K)) :=
      ⟨((invariantModel H X).openSubvariety V).toSpec⟩
    letI : IsIntegral ((invariantModel H X).openSubvariety V).scheme := by
      have : IsOpenImmersion V.ι := (invariantModel H X).openInclusion_isOpenImmersion V
      exact (show IsIntegral V.toScheme from isIntegral_of_isOpenImmersion V.ι)
    ((invariantModel H X).openSubvariety V).scheme.functionField ≃ₐ[K]
      invariantField H Z := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : Z.scheme.Over (Spec (.of K)) := ⟨Z.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Z.scheme := isIntegral_of_irreducibleSpace_of_isReduced Z.scheme
  let Y := invariantModel H X
  let W := Y.openSubvariety V
  let _ : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
  let _ : W.scheme.Over (Spec (.of K)) := ⟨W.toSpec⟩
  have : IsOpenImmersion V.ι := Y.openInclusion_isOpenImmersion V
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral W.scheme := inferInstanceAs (IsIntegral V.toScheme)
  let j : W.scheme ⟶ Y.scheme := V.ι
  have : IsOpenImmersion j := (invariantModel H X).openInclusion_isOpenImmersion V
  have : IsDominant j := Opens.isDominant_ι (V.isOpen.dense (Set.nonempty_coe_sort.mp
    (inferInstance : Nonempty V)))
  have : j.IsOver (Spec (.of K)) := ⟨(Y.openInclusion V).w⟩
  exact ((openFunctionFieldAlgEquiv K j).symm.trans (invariantModelFieldEquiv H X)).trans
    (invariantFieldOpenEquiv H Z X i)

/-- For a morphism factoring the invariant map on an equivariant open subvariety,
the canonical invariant-field identification is its function-field pullback. -/
theorem invariantOpenFieldEquiv_apply
    (d : Z.toOver ⟶ (invariantDomain H X).toOver) [IsDominant d.left]
    (q : Z.toOver ⟶ ((invariantModel H X).openSubvariety V).toOver)
    [IsDominant q.left]
    (hdi : d ≫ X.openInclusion (invariantMap H X).domain = i)
    (hqd : q ≫ (invariantModel H X).openInclusion V = d ≫ invariantMorphism H X) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : Z.scheme.Over (Spec (.of K)) := ⟨Z.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : IsIntegral Z.scheme := isIntegral_of_irreducibleSpace_of_isReduced Z.scheme
    letI : (invariantModel H X).scheme.Over (Spec (.of K)) :=
      ⟨(invariantModel H X).toSpec⟩
    letI : ((invariantModel H X).openSubvariety V).scheme.Over (Spec (.of K)) :=
      ⟨((invariantModel H X).openSubvariety V).toSpec⟩
    letI : IsIntegral ((invariantModel H X).openSubvariety V).scheme := by
      have : IsOpenImmersion V.ι := (invariantModel H X).openInclusion_isOpenImmersion V
      exact (show IsIntegral V.toScheme from isIntegral_of_isOpenImmersion V.ι)
    ∀ a, (invariantOpenFieldEquiv H X Z V i a).val =
      functionFieldMap (X := Z.scheme)
        (Y := ((invariantModel H X).openSubvariety V).scheme) q.left a := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : Z.scheme.Over (Spec (.of K)) := ⟨Z.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Z.scheme := isIntegral_of_irreducibleSpace_of_isReduced Z.scheme
  let Y := invariantModel H X
  let W := Y.openSubvariety V
  let D := invariantDomain H X
  let _ : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
  let _ : W.scheme.Over (Spec (.of K)) := ⟨W.toSpec⟩
  have : IsOpenImmersion V.ι := Y.openInclusion_isOpenImmersion V
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral W.scheme := inferInstanceAs (IsIntegral V.toScheme)
  have : Nonempty (invariantMap H X).domain :=
    Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  have : IsDominant (invariantMap H X).domain.ι :=
    Opens.isDominant_ι (invariantMap H X).dense_domain
  let j : W.scheme ⟶ Y.scheme := V.ι
  have : IsOpenImmersion j := (invariantModel H X).openInclusion_isOpenImmersion V
  have : IsDominant j := Opens.isDominant_ι (V.isOpen.dense (Set.nonempty_coe_sort.mp
    (inferInstance : Nonempty V)))
  have : j.IsOver (Spec (.of K)) := ⟨(Y.openInclusion V).w⟩
  let ir : Z.scheme ⟶ X.scheme := i.left
  let dr : Z.scheme ⟶ D.scheme := d.left
  let qr : Z.scheme ⟶ W.scheme := q.left
  let k : D.scheme ⟶ X.scheme := (invariantMap H X).domain.ι
  let f : D.scheme ⟶ Y.scheme := (invariantMorphism H X).left
  have : IsDominant ir := inferInstanceAs (IsDominant i.left)
  have : IsDominant dr := inferInstanceAs (IsDominant d.left)
  have : IsDominant qr := inferInstanceAs (IsDominant q.left)
  have : IsDominant k := Opens.isDominant_ι (invariantMap H X).dense_domain
  have : IsDominant f := invariantMorphism_dominant H X
  have hq : qr ≫ j = dr ≫ f := congrArg Over.Hom.left hqd
  have hi : dr ≫ k = ir := congrArg Over.Hom.left hdi
  have hm := invariantMorphism_fieldMap H X
  change functionFieldMap f = (functionFieldMap k).comp
    ((invariantField H X).val.toRingHom.comp
      (invariantModelFieldEquiv H X).toRingHom) at hm
  have hp := functionFieldMap_congr (qr ≫ j) (dr ≫ f) hq
  rw [functionFieldMap_comp, functionFieldMap_comp, hm] at hp
  have hi' : (functionFieldMap dr).comp (functionFieldMap k) = functionFieldMap ir := by
    rw [← functionFieldMap_comp]
    exact functionFieldMap_congr _ _ hi
  intro a
  let b := (openFunctionFieldAlgEquiv K j).symm a
  have hb : functionFieldMap j b = a :=
    (openFunctionFieldAlgEquiv K j).apply_symm_apply a
  have hz : (invariantOpenFieldEquiv H X Z V i a).val =
      functionFieldMap ir ((invariantModelFieldEquiv H X b).val) := by
    rfl
  rw [hz]
  have hh := RingHom.congr_fun hp b
  change functionFieldMap qr (functionFieldMap j b) =
    functionFieldMap dr (functionFieldMap k ((invariantModelFieldEquiv H X b).val)) at hh
  rw [hb] at hh
  exact (RingHom.congr_fun hi' ((invariantModelFieldEquiv H X b).val)).symm.trans hh.symm

end

end GroupActions.Variety
