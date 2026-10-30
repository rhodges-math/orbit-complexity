import OrbitComplexity.FrobeniusSplitting.Splittings.Restriction
import OrbitComplexity.FrobeniusSplitting.Splittings.Transport
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing local Frobenius splittings

Splittings on an open cover glue if their section formulas agree on overlaps.
The construction uses unique gluing of sections of the structure sheaf; all
splitting identities and restriction identities are checked on the cover.

## Main definitions

* `FrobeniusSplitting.SchemeSplitting.onSubopen`: ambient section formulas.
* `FrobeniusSplitting.SchemeSplitting.glue`: gluing compatible chart splittings.

## Main results

* `FrobeniusSplitting.SchemeSplitting.glue_restrict`: the prescribed restrictions.
* `FrobeniusSplitting.SchemeSplitting.glue_unique`: uniqueness of the gluing.
-/

noncomputable section

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme} {p : ℕ}

/-- A splitting on an open subscheme acts on each ambient open subset contained in it. -/
def onSubopen {U : X.Opens} (splitting : SchemeSplitting U.toScheme p)
    (V : X.Opens) (h : V ≤ U) : RingSplitting Γ(X, V) p := by
  have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using h)
  exact (splitting.onOpen (U.ι ⁻¹ᵁ V)).transport
    (asIso (U.ι.app V)).symm.commRingCatIsoToRingEquiv

/-- The structure sheaf map identifies the ambient and local splitting formulas. -/
theorem onSubopen_app {U : X.Opens} (splitting : SchemeSplitting U.toScheme p)
    (V : X.Opens) (h : V ≤ U) (s : Γ(X, V)) :
    U.ι.app V (splitting.onSubopen V h s) =
      splitting.onOpen (U.ι ⁻¹ᵁ V) (U.ι.app V s) := by
  have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using h)
  exact (asIso (U.ι.app V)).commRingCatIsoToRingEquiv.apply_symm_apply _

/-- Ambient section formulas obtained from an open splitting commute with restriction. -/
theorem onSubopen_restrict {U : X.Opens} (splitting : SchemeSplitting U.toScheme p)
    {V W : X.Opens} (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(X, V)) :
    splitting.onSubopen W (hWV.trans hV) (X.presheaf.map (homOfLE hWV).op s) =
      X.presheaf.map (homOfLE hWV).op (splitting.onSubopen V hV s) := by
  have : IsIso (U.ι.app W) := U.ι.isIso_app W (by simpa using hWV.trans hV)
  have hpre : U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ V := fun _ hx ↦ hWV hx
  have hnat (a : Γ(X, V)) :
      U.ι.app W (X.presheaf.map (homOfLE hWV).op a) =
        U.toScheme.presheaf.map (homOfLE hpre).op (U.ι.app V a) :=
    congrArg (fun f : Γ(X, V) ⟶ Γ(U.toScheme, U.ι ⁻¹ᵁ W) ↦ f a)
      (U.ι.naturality (homOfLE hWV).op)
  apply (asIso (U.ι.app W)).commRingCatIsoToRingEquiv.injective
  change U.ι.app W _ = U.ι.app W _
  rw [onSubopen_app, hnat, splitting.restrict_comm hpre, hnat, onSubopen_app]

/-- Passing from an open subscheme to its image recovers the original section formula. -/
theorem onSubopen_image {U : X.Opens} (splitting : SchemeSplitting U.toScheme p)
    (V : U.toScheme.Opens) :
    splitting.onSubopen (U.ι ''ᵁ V) (U.ι_image_le V) = splitting.onOpen V := by
  have : IsIso (U.ι.app (U.ι ''ᵁ V)) := inferInstance
  ext s
  apply (asIso (U.ι.app (U.ι ''ᵁ V))).commRingCatIsoToRingEquiv.injective
  change U.ι.app (U.ι ''ᵁ V) _ = U.ι.app (U.ι ''ᵁ V) _
  rw [onSubopen_app]
  have happ : U.ι.app (U.ι ''ᵁ V) = U.toScheme.presheaf.map
      (homOfLE (Scheme.Hom.preimage_image_eq U.ι V).le).op := rfl
  rw [happ]
  exact splitting.restrict_comm _ s

/-- Restriction followed by ambient identification recovers the original splitting. -/
theorem restrict_onSubopen (splitting : SchemeSplitting X p) (U V : X.Opens)
    (h : V ≤ U) : (splitting.restrict U).onSubopen V h = splitting.onOpen V := by
  have : IsIso (U.ι.app V) := U.ι.isIso_app V (by simpa using h)
  ext s
  apply (asIso (U.ι.app V)).commRingCatIsoToRingEquiv.injective
  change U.ι.app V _ = U.ι.app V _
  rw [onSubopen_app]
  exact splitting.restrict_comm (Set.image_preimage_subset _ _) s

variable {ι : Type*} (U : ι → X.Opens)
    (splitting : ∀ i, SchemeSplitting (U i).toScheme p)
    (compatible : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j),
      (splitting i).onSubopen V hi = (splitting j).onSubopen V hj)

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
      (fun i ↦ (splitting i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s)) := by
  intro i j
  change X.presheaf.map (homOfLE (inf_le_left :
      (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op
      ((splitting i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s)) =
    X.presheaf.map (homOfLE (inf_le_right :
      (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op
      ((splitting j).onSubopen (W ⊓ U j) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s))
  rw [← onSubopen_restrict (splitting i) inf_le_right inf_le_left,
    ← onSubopen_restrict (splitting j) inf_le_right inf_le_right]
  have heq := compatible i j ((W ⊓ U i) ⊓ (W ⊓ U j))
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [heq]
  congr 1
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem exists_glue (hcover : iSup U = ⊤) (W : X.Opens) (s : Γ(X, W)) :
    ∃! t : Γ(X, W), ∀ i, X.presheaf.map (homOfLE inf_le_left).op t =
      (splitting i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s) :=
  X.sheaf.existsUnique_gluing' (fun i ↦ W ⊓ U i) W
    (fun _ ↦ homOfLE inf_le_left) (cover_inter U hcover W) _
    (section_compatible U splitting compatible W s)

private def glueSection (hcover : iSup U = ⊤) (W : X.Opens) (s : Γ(X, W)) : Γ(X, W) :=
  (exists_glue U splitting compatible hcover W s).choose

private theorem glueSection_restrict (hcover : iSup U = ⊤) (W : X.Opens)
    (s : Γ(X, W)) (i : ι) :
    X.presheaf.map (homOfLE inf_le_left).op (glueSection U splitting compatible hcover W s) =
      (splitting i).onSubopen (W ⊓ U i) inf_le_right
        (X.presheaf.map (homOfLE inf_le_left).op s) :=
  (exists_glue U splitting compatible hcover W s).choose_spec.1 i

/-- Compatible local splittings on an open cover define a splitting of the scheme. -/
def glue (hcover : iSup U = ⊤) : SchemeSplitting X p where
  onOpen W :=
    { toAddMonoidHom :=
        { toFun := glueSection U splitting compatible hcover W
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
        change glueSection U splitting compatible hcover W (a ^ p * b) =
          a * glueSection U splitting compatible hcover W b
        apply sections_ext U hcover W
        intro i
        rw [glueSection_restrict, map_mul, map_pow,
          RingSplitting.map_pow_mul, map_mul, glueSection_restrict]
      map_one' := by
        change glueSection U splitting compatible hcover W 1 = 1
        apply sections_ext U hcover W
        intro i
        rw [glueSection_restrict]
        simp }
  restrict_comm {V W} h s := by
    change glueSection U splitting compatible hcover W
      (X.presheaf.map (homOfLE h).op s) =
        X.presheaf.map (homOfLE h).op (glueSection U splitting compatible hcover V s)
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
    exact (splitting i).onSubopen_restrict inf_le_right hle _

/-- The glued splitting has the prescribed formula on every open subset of a chart. -/
theorem glue_onSubopen (hcover : iSup U = ⊤) (i : ι) (V : X.Opens)
    (hi : V ≤ U i) (s : Γ(X, V)) :
    (glue U splitting compatible hcover).onOpen V s =
      (splitting i).onSubopen V hi s := by
  change glueSection U splitting compatible hcover V s = _
  apply sections_ext U hcover V
  intro j
  rw [glueSection_restrict, ← onSubopen_restrict]
  exact congrArg (fun σ : RingSplitting Γ(X, V ⊓ U j) p ↦
    σ (X.presheaf.map (homOfLE inf_le_left).op s))
    (compatible j i (V ⊓ U j) inf_le_right (inf_le_left.trans hi))

/-- Restricting the glued splitting to a chart gives the specified local splitting. -/
theorem glue_restrict (hcover : iSup U = ⊤) (i : ι) :
    (glue U splitting compatible hcover).restrict (U i) = splitting i := by
  ext V s
  change (glue U splitting compatible hcover).onOpen ((U i).ι ''ᵁ V) s = _
  exact (glue_onSubopen U splitting compatible hcover i _ ((U i).ι_image_le V) s).trans
    (congrArg (fun σ : RingSplitting Γ(X, (U i).ι ''ᵁ V) p ↦ σ s)
      (onSubopen_image (splitting i) V))

/-- A splitting with the prescribed chart formulas is the glued splitting. -/
theorem glue_unique (hcover : iSup U = ⊤) (other : SchemeSplitting X p)
    (hother : ∀ i, other.restrict (U i) = splitting i) :
    other = glue U splitting compatible hcover := by
  ext V s
  apply sections_ext U hcover V
  intro i
  change X.presheaf.map (homOfLE inf_le_left).op (other.onOpen V s) =
    X.presheaf.map (homOfLE inf_le_left).op
      (glueSection U splitting compatible hcover V s)
  rw [glueSection_restrict, ← other.restrict_comm inf_le_left,
    ← hother, restrict_onSubopen]

end FrobeniusSplitting.SchemeSplitting
