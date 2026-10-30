import OrbitComplexity.FrobeniusSplitting.Modules.RelativeScalars
import OrbitComplexity.FrobeniusSplitting.Modules.FunctionsBaseChange

/-! # Pullback of relative functions over an open base -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable {P X U Y : Scheme.{u}} (p : P ⟶ U) (k : P ⟶ X)
  (j : U ⟶ Y) (q : X ⟶ Y) [IsOpenImmersion j] (h : p ≫ j = k ≫ q)

include h in
private theorem squarePreimage (V : U.Opens) :
    p ⁻¹ᵁ V ≤ k ⁻¹ᵁ (q ⁻¹ᵁ j ''ᵁ V) := by
  change p ⁻¹ᵁ V ≤ (k ≫ q) ⁻¹ᵁ j ''ᵁ V
  rw [← h]
  change p ⁻¹ᵁ V ≤ p ⁻¹ᵁ (j ⁻¹ᵁ j ''ᵁ V)
  rw [j.preimage_image_eq]

private theorem squareScalar (V : U.Opens) :
    (j.appIso V).inv ≫ q.app (j ''ᵁ V) ≫
        k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q
            h V) =
      p.app V := by
  apply (cancel_epi (j.appIso V).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appIso_hom',
    Scheme.Hom.appLE_comp_appLE, h]

private theorem squareNatural {V W : U.Opens} (t : V ⟶ W) :
    X.presheaf.map ((Opens.map q.base).map (j.opensFunctor.map t)).op ≫
        k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q
            h V) =
      k.appLE (q ⁻¹ᵁ j ''ᵁ W) (p ⁻¹ᵁ W) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h
          W) ≫
        P.presheaf.map ((Opens.map p.base).map t).op := by
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- A regular square over an open immersion pulls back the original relative functions. -/
def openFunctionsPullback :
    (Scheme.Modules.restrictFunctor j).obj (FrobeniusSplitting.CharacterLine.relativeFunctionsObj
        Y (Over.mk q)) ⟶
      FrobeniusSplitting.CharacterLine.relativeFunctionsObj U (Over.mk p) where
  val.app V :=
    { hom' :=
      { toFun := fun s => k.appLE (q ⁻¹ᵁ j ''ᵁ V.unop) (p ⁻¹ᵁ V.unop)
          (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h V.unop) s
        map_add' := fun s t => map_add _ s t
        map_smul' := by
          intro (r : Γ(U, V.unop)) (s : Γ(X, q ⁻¹ᵁ j ''ᵁ V.unop))
          let phi : Γ(X, q ⁻¹ᵁ j ''ᵁ V.unop) →+* Γ(P, p ⁻¹ᵁ V.unop) :=
            (k.appLE (q ⁻¹ᵁ j ''ᵁ V.unop) (p ⁻¹ᵁ V.unop)
              (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h V.unop)).hom
          let rX : Γ(X, q ⁻¹ᵁ j ''ᵁ V.unop) :=
            q.app (j ''ᵁ V.unop) ((j.appIso V.unop).inv r)
          let rP : Γ(P, p ⁻¹ᵁ V.unop) := p.app V.unop r
          change phi (rX * s) = rP * phi s
          exact (map_mul phi rX s).trans (congrArg (fun a => a * phi s)
            (ConcreteCategory.congr_hom (FrobeniusSplitting.CharacterLine.squareScalar p k j q h
                V.unop) r)) } }
  val.naturality {V W} t := by
    ext s
    exact ConcreteCategory.congr_hom (FrobeniusSplitting.CharacterLine.squareNatural p k j q h
        t.unop) s

/-- On every open this is the original scheme map on the specified inverse-image opens. -/
theorem openFunctionsPullback_app (V : U.Opens) (s : Γ(X, q ⁻¹ᵁ j ''ᵁ V)) :
    ((FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q h).val.app (.op V)).hom s =
      k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h
          V) s := rfl

/-- Multiplication by an original function pulls back by the same regular scheme morphism. -/
theorem openFunctionsPullback_smul (r : Γ(X, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map
        (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul Y (Over.mk q) r) ≫
            FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q h =
      FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q h ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p) (k.appTop r) := by
  ext V s
  change Γ(X, q ⁻¹ᵁ j ''ᵁ V) at s
  let phi : Γ(X, q ⁻¹ᵁ j ''ᵁ V) →+* Γ(P, p ⁻¹ᵁ V) :=
    (k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h
        V)).hom
  let rX : Γ(X, q ⁻¹ᵁ j ''ᵁ V) := X.presheaf.map (q ⁻¹ᵁ j ''ᵁ V).leTop.op r
  let rP : Γ(P, p ⁻¹ᵁ V) := P.presheaf.map (p ⁻¹ᵁ V).leTop.op (k.appTop r)
  change phi (rX * s) = rP * phi s
  have ht : (⊤ : P.Opens) ≤ k ⁻¹ᵁ (⊤ : X.Opens) := by
    rw [Scheme.Hom.preimage_top]
  have htop : k.appLE ⊤ ⊤ ht = k.appTop := by
    unfold Scheme.Hom.appLE
    have hi : (homOfLE ht).op = 𝟙 (op (⊤ : P.Opens)) := Subsingleton.elim _ _
    rw [hi]
    exact (congrArg (fun f => k.appTop ≫ f)
      (CategoryTheory.Functor.map_id P.presheaf (op (⊤ : P.Opens)))).trans
        (Category.comp_id k.appTop)
  have hr : X.presheaf.map (q ⁻¹ᵁ j ''ᵁ V).leTop.op ≫
      k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h
          V) =
      k.appTop ≫ P.presheaf.map (p ⁻¹ᵁ V).leTop.op := by
    calc
      _ = k.appLE ⊤ (p ⁻¹ᵁ V) _ :=
        k.map_appLE (FrobeniusSplitting.CharacterLine.squarePreimage p k j q h V) (q ⁻¹ᵁ j ''ᵁ
            V).leTop.op
      _ = k.appLE ⊤ ⊤ ht ≫ P.presheaf.map (p ⁻¹ᵁ V).leTop.op :=
        (k.appLE_map ht (p ⁻¹ᵁ V).leTop.op).symm
      _ = _ := congrArg (fun f => f ≫ P.presheaf.map (p ⁻¹ᵁ V).leTop.op) htop
  exact (map_mul phi rX s).trans
    (congrArg (fun a => a * phi s) (ConcreteCategory.congr_hom hr r))

/-- For the Cartesian square this map is the canonical open base-change isomorphism. -/
theorem openFunctionsBaseChange_hom [IsOpenImmersion k] (H : IsPullback p k j q) :
    (FrobeniusSplitting.CharacterLine.openFunctionsBaseChange p k j q H).hom =
        FrobeniusSplitting.CharacterLine.openFunctionsPullback p k j q H.w := by
  ext V s
  change ((X.presheaf.map (eqToHom
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V)).op ≫
      (k.appIso (p ⁻¹ᵁ V)).hom) s) = k.appLE _ _ _ s
  have hr : X.presheaf.map (eqToHom
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V)).op ≫
      (k.appIso (p ⁻¹ᵁ V)).hom =
      k.appLE (q ⁻¹ᵁ j ''ᵁ V) (p ⁻¹ᵁ V) (FrobeniusSplitting.CharacterLine.squarePreimage p k j q
          H.w V) := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  exact ConcreteCategory.congr_hom hr s

end FrobeniusSplitting.CharacterLine
