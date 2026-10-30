import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing Frobenius-linear structure-sheaf operators

Operators on the members of an open cover glue when their section formulas agree on overlaps.
The sheaf gluing theorem supplies the section maps, and the operator identities are verified
on the cover. No normalization at one is needed for this gluing construction.
-/

noncomputable section

namespace FrobeniusSplitting.SchemeFrobeniusMap

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme} {p : ℕ}

/-- An operator on an open subscheme acts on each ambient open subset contained in it. -/
def onSubopen {U : X.Opens} (operator : SchemeFrobeniusMap U.toScheme p)
    (V : X.Opens) (h : V ≤ U) : FrobeniusLinearMap Γ(X, V) p := by
  have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using h)
  exact (operator.onOpen (U.ι ⁻¹ᵁ V)).transport
    (asIso (U.ι.app V)).symm.commRingCatIsoToRingEquiv

/-- The structure sheaf map identifies the ambient and local operator formulas. -/
theorem onSubopen_app {U : X.Opens} (operator : SchemeFrobeniusMap U.toScheme p)
    (V : X.Opens) (h : V ≤ U) (s : Γ(X, V)) :
    U.ι.app V (operator.onSubopen V h s) =
      operator.onOpen (U.ι ⁻¹ᵁ V) (U.ι.app V s) := by
  have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using h)
  exact (asIso (U.ι.app V)).commRingCatIsoToRingEquiv.apply_symm_apply _

/-- Ambient section formulas obtained from an open operator commute with restriction. -/
theorem onSubopen_restrict {U : X.Opens} (operator : SchemeFrobeniusMap U.toScheme p)
    {V W : X.Opens} (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(X, V)) :
    operator.onSubopen W (hWV.trans hV) (X.presheaf.map (homOfLE hWV).op s) =
      X.presheaf.map (homOfLE hWV).op (operator.onSubopen V hV s) := by
  have : IsIso (U.ι.app W) := U.ι.isIso_app W (by simpa using hWV.trans hV)
  have hpre : U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ V := fun _ hx ↦ hWV hx
  have hnat (a : Γ(X, V)) :
      U.ι.app W (X.presheaf.map (homOfLE hWV).op a) =
        U.toScheme.presheaf.map (homOfLE hpre).op (U.ι.app V a) :=
    congrArg (fun f : Γ(X, V) ⟶ Γ(U.toScheme, U.ι ⁻¹ᵁ W) ↦ f a)
      (U.ι.naturality (homOfLE hWV).op)
  apply (asIso (U.ι.app W)).commRingCatIsoToRingEquiv.injective
  change U.ι.app W _ = U.ι.app W _
  rw [onSubopen_app, hnat, operator.restrict_comm hpre, hnat, onSubopen_app]

/-- Passing from an open subscheme to its image recovers the original section formula. -/
theorem onSubopen_image {U : X.Opens} (operator : SchemeFrobeniusMap U.toScheme p)
    (V : U.toScheme.Opens) :
    operator.onSubopen (U.ι ''ᵁ V) (U.ι_image_le V) = operator.onOpen V := by
  have : IsIso (U.ι.app (U.ι ''ᵁ V)) := inferInstance
  ext s
  apply (asIso (U.ι.app (U.ι ''ᵁ V))).commRingCatIsoToRingEquiv.injective
  change U.ι.app (U.ι ''ᵁ V) _ = U.ι.app (U.ι ''ᵁ V) _
  rw [onSubopen_app]
  have happ : U.ι.app (U.ι ''ᵁ V) = U.toScheme.presheaf.map
      (homOfLE (Scheme.Hom.preimage_image_eq U.ι V).le).op := rfl
  rw [happ]
  exact operator.restrict_comm _ s

/-- Restriction followed by ambient identification recovers the original operator. -/
theorem restrict_onSubopen (operator : SchemeFrobeniusMap X p) (U V : X.Opens)
    (h : V ≤ U) : (operator.restrict U).onSubopen V h = operator.onOpen V := by
  have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using h)
  ext s
  apply (asIso (U.ι.app V)).commRingCatIsoToRingEquiv.injective
  change U.ι.app V _ = U.ι.app V _
  rw [onSubopen_app]
  exact operator.restrict_comm (Set.image_preimage_subset _ _) s

variable {ι : Type*} (U : ι → X.Opens)
    (operator : ∀ i, SchemeFrobeniusMap (U i).toScheme p)
    (compatible : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      (operator i).onSubopen V hi = (operator j).onSubopen V hj)

private theorem cover_inter (hcover : iSup U = ⊤) (W : X.Opens) :
    W ≤ ⨆ i, W ⊓ U i := by
  rw [← inf_iSup_eq, hcover, inf_top_eq]

private theorem sections_ext (hcover : iSup U = ⊤) (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ i, X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op a =
      X.presheaf.map (homOfLE inf_le_left).op b) : a = b :=
  X.sheaf.eq_of_locally_eq' (fun i ↦ W ⊓ U i) W
    (fun _ ↦ homOfLE inf_le_left) (cover_inter U hcover W) a b h

include compatible

private theorem section_compatible (W : X.Opens) (s : Γ(X, W)) :
    TopCat.Presheaf.IsCompatible X.presheaf (fun i ↦ W ⊓ U i)
      (fun i ↦ (operator i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s)) := by
  intro i j
  change X.presheaf.map (homOfLE (inf_le_left :
      (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op
      ((operator i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s)) =
    X.presheaf.map (homOfLE (inf_le_right :
      (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op
      ((operator j).onSubopen (W ⊓ U j) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s))
  rw [← onSubopen_restrict (operator i) inf_le_right inf_le_left,
    ← onSubopen_restrict (operator j) inf_le_right inf_le_right]
  have heq := compatible i j ((W ⊓ U i) ⊓ (W ⊓ U j))
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [heq]
  congr 1
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem exists_glue (hcover : iSup U = ⊤) (W : X.Opens) (s : Γ(X, W)) :
    ∃! t : Γ(X, W), ∀ i, X.presheaf.map (homOfLE inf_le_left).op t =
      (operator i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s) :=
  X.sheaf.existsUnique_gluing' (fun i ↦ W ⊓ U i) W
    (fun _ ↦ homOfLE inf_le_left) (cover_inter U hcover W) _
    (section_compatible U operator compatible W s)

private def glueSection (hcover : iSup U = ⊤) (W : X.Opens) (s : Γ(X, W)) : Γ(X, W) :=
  (exists_glue U operator compatible hcover W s).choose

private theorem glueSection_restrict (hcover : iSup U = ⊤) (W : X.Opens)
    (s : Γ(X, W)) (i : ι) :
    X.presheaf.map (homOfLE inf_le_left).op (glueSection U operator compatible hcover W s) =
      (operator i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s) :=
  (exists_glue U operator compatible hcover W s).choose_spec.1 i

/-- Compatible local operators on an open cover define a operator of the scheme. -/
def glue (hcover : iSup U = ⊤) : SchemeFrobeniusMap X p where
  onOpen W :=
    { toAddMonoidHom :=
        { toFun := glueSection U operator compatible hcover W
          map_zero' := by
            apply sections_ext U hcover W
            intro i
            rw [glueSection_restrict]
            simp
          map_add' := by
            intro a b
            apply sections_ext U hcover W
            intro i
            simp only [glueSection_restrict, map_add] }
      map_pow_mul' := by
        intro a b
        change glueSection U operator compatible hcover W (a ^ p * b) =
          a * glueSection U operator compatible hcover W b
        apply sections_ext U hcover W
        intro i
        rw [glueSection_restrict, map_mul, map_pow,
          FrobeniusLinearMap.map_pow_mul, map_mul, glueSection_restrict] }
  restrict_comm {V W} h s := by
    change glueSection U operator compatible hcover W
      (X.presheaf.map (homOfLE h).op s) =
        X.presheaf.map (homOfLE h).op (glueSection U operator compatible hcover V s)
    apply sections_ext U hcover W
    intro i
    have hle : W ⊓ U i ≤ V ⊓ U i := inf_le_inf h le_rfl
    have hres (a : Γ(X, V)) :
        X.presheaf.map (homOfLE inf_le_left).op
          (X.presheaf.map (homOfLE h).op a) =
            X.presheaf.map (homOfLE hle).op
              (X.presheaf.map (homOfLE inf_le_left).op a) := by
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [glueSection_restrict, hres, hres, glueSection_restrict]
    exact (operator i).onSubopen_restrict inf_le_right hle _

/-- The glued operator has the prescribed formula on every open subset of a chart. -/
theorem glue_onSubopen (hcover : iSup U = ⊤) (i : ι) (V : X.Opens)
    (hi : V ≤ U i) (s : Γ(X, V)) :
    (glue U operator compatible hcover).onOpen V s =
      (operator i).onSubopen V hi s := by
  change glueSection U operator compatible hcover V s = _
  apply sections_ext U hcover V
  intro j
  rw [glueSection_restrict, ← onSubopen_restrict]
  exact congrArg (fun σ : FrobeniusLinearMap Γ(X, V ⊓ U j) p ↦
    σ (X.presheaf.map (homOfLE inf_le_left).op s))
    (compatible j i (V ⊓ U j) inf_le_right (inf_le_left.trans hi))

/-- Restricting the glued operator to a chart gives the specified local operator. -/
theorem glue_restrict (hcover : iSup U = ⊤) (i : ι) :
    (glue U operator compatible hcover).restrict (U i) = operator i := by
  ext V s
  change (glue U operator compatible hcover).onOpen ((U i).ι ''ᵁ V) s = _
  exact (glue_onSubopen U operator compatible hcover i _ ((U i).ι_image_le V) s).trans
    (congrArg (fun σ : FrobeniusLinearMap Γ(X, (U i).ι ''ᵁ V) p ↦ σ s)
      (onSubopen_image (operator i) V))

/-- An operator with the prescribed chart formulas is the glued operator. -/
theorem glue_unique (hcover : iSup U = ⊤) (other : SchemeFrobeniusMap X p)
    (hother : ∀ i, other.restrict (U i) = operator i) :
    other = glue U operator compatible hcover := by
  ext V s
  apply sections_ext U hcover V
  intro i
  change X.presheaf.map (homOfLE inf_le_left).op (other.onOpen V s) =
    X.presheaf.map (homOfLE inf_le_left).op
      (glueSection U operator compatible hcover V s)
  rw [glueSection_restrict, ← other.restrict_comm inf_le_left,
    ← hother, restrict_onSubopen]

end FrobeniusSplitting.SchemeFrobeniusMap
