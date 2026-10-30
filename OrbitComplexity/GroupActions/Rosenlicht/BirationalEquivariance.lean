import OrbitComplexity.GroupActions.Rosenlicht.RationalEquivariance
import OrbitComplexity.GroupActions.Rosenlicht.BirationalFields

/-!
# Function-field equivariance of birational maps

A partial isomorphism gives a function-field isomorphism by pullback. Equality
of translated rational maps implies equivariance of this isomorphism by
cancellation of the canonical generic-point morphism.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u v

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- Pullback along a partial isomorphism identifies the function fields of its
source and target. -/
def partialIsoPullback (f : X.PartialIso Y) :
    Y.functionField ≃+* X.functionField := by
  haveI : Nonempty f.source := f.dense_source.nonempty.to_subtype
  haveI : Nonempty f.target := f.dense_target.nonempty.to_subtype
  letI : IrreducibleSpace f.source.toScheme := f.source.ι.isOpenEmbedding.irreducibleSpace
  letI : IrreducibleSpace f.target.toScheme := f.target.ι.isOpenEmbedding.irreducibleSpace
  letI : IsDominant f.source.ι := Opens.isDominant_ι f.dense_source
  letI : IsDominant f.target.ι := Opens.isDominant_ι f.dense_target
  exact (openFunctionFieldEquiv (f.iso.hom ≫ f.target.ι)).trans
    (openFunctionFieldEquiv f.source.ι).symm

/-- Function-field pullback represents the generic restriction of a partial
isomorphism. -/
theorem partialIsoPullback_generic (f : X.PartialIso Y) :
    f.toPartialMap.fromFunctionField =
      Spec.map (CommRingCat.ofHom (partialIsoPullback f).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) := by
  have : Nonempty f.source := f.dense_source.nonempty.to_subtype
  have : Nonempty f.target := f.dense_target.nonempty.to_subtype
  let : IrreducibleSpace f.source.toScheme := f.source.ι.isOpenEmbedding.irreducibleSpace
  let : IrreducibleSpace f.target.toScheme := f.target.ι.isOpenEmbedding.irreducibleSpace
  let : IsDominant f.source.ι := Opens.isDominant_ι f.dense_source
  let : IsDominant f.target.ι := Opens.isDominant_ι f.dense_target
  let a := openFunctionFieldEquiv f.source.ι
  have hx : genericPoint X ∈ f.source :=
    ((genericPoint_spec X).mem_open_set_iff f.source.isOpen).mpr
      (by simpa using f.dense_source.nonempty)
  have lift : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      f.source.fromSpecStalkOfMem (genericPoint X) hx =
        f.source.toScheme.fromSpecStalk (genericPoint f.source.toScheme) := by
    apply (cancel_mono f.source.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_genericPoint f.source.ι
  have he : (functionFieldMap f.source.ι).comp (partialIsoPullback f).toRingHom =
      functionFieldMap (f.iso.hom ≫ f.target.ι) := by
    ext b
    exact a.apply_symm_apply _
  let i := a.toCommRingCatIso
  have : IsIso (CommRingCat.ofHom a.toRingHom) := inferInstanceAs (IsIso i.hom)
  apply (cancel_epi (Spec.map (CommRingCat.ofHom a.toRingHom))).mp
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      (f.source.fromSpecStalkOfMem (genericPoint X) hx ≫ f.iso.hom ≫ f.target.ι) = _
  rw [← Category.assoc, lift]
  rw [← Spec.map_comp_assoc]
  change f.source.toScheme.fromSpecStalk (genericPoint f.source.toScheme) ≫
      f.iso.hom ≫ f.target.ι =
    Spec.map (CommRingCat.ofHom
      ((functionFieldMap f.source.ι).comp (partialIsoPullback f).toRingHom)) ≫ _
  rw [he, functionFieldMap_genericPoint]

/-- Equivariance of a birational rational map implies equivariance of its
function-field pullback isomorphism. -/
theorem partialIsoPullback_equivariant {M : Type v} [Monoid M]
    (ρ : M →* Aut X) (σ : M →* Aut Y) (f : X.PartialIso Y)
    (hf : RationalEquivariant ρ σ f.toPartialMap) (m : M) (b : Y.functionField) :
    letI := functionFieldAction ρ
    letI := functionFieldAction σ
    partialIsoPullback f (m • b) = m • partialIsoPullback f b := by
  let e := partialIsoPullback f
  have he := rationalEquivariant_generic ρ σ f.toPartialMap hf m
  rw [partialIsoPullback_generic, Category.assoc,
    ← functionFieldMap_genericPoint (σ m).inv] at he
  have hs : Spec.map (CommRingCat.ofHom
        ((functionFieldMap (ρ m).inv).comp e.toRingHom)) =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (functionFieldMap (σ m).inv))) := by
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using he
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact congrArg (fun k : Y.functionField →+* X.functionField ↦ k b) hc.symm

section BaseRing

variable (K : Type u) [CommRing K]
variable [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [IsIntegral X] [IsIntegral Y]

/-- Pullback along a partial isomorphism over an affine base identifies its
function fields as algebras over the base ring. -/
def partialIsoPullbackAlgEquiv (f : X.PartialIso Y)
    (hf : f.IsOver (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))) :
    Y.functionField ≃ₐ[K] X.functionField := by
  haveI : Nonempty f.source := f.dense_source.nonempty.to_subtype
  haveI : Nonempty f.target := f.dense_target.nonempty.to_subtype
  letI : IsDominant f.source.ι := Opens.isDominant_ι f.dense_source
  letI : IsDominant f.target.ι := Opens.isDominant_ι f.dense_target
  letI : (f.iso.hom ≫ f.target.ι).IsOver (Spec (.of K)) := ⟨by
    change (f.iso.hom ≫ f.target.ι) ≫ (Y ↘ Spec (.of K)) =
      f.source.ι ≫ (X ↘ Spec (.of K))
    simpa only [Category.assoc] using hf⟩
  exact (openFunctionFieldAlgEquiv K (f.iso.hom ≫ f.target.ι)).trans
    (openFunctionFieldAlgEquiv K f.source.ι).symm

end BaseRing

end

end GroupActions
