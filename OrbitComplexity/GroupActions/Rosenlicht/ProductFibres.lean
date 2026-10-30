import OrbitComplexity.GroupActions.Rosenlicht.PointFibres
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Product fibres over rational points

The fibre of a product projection over a rational point is the other factor.
The identifications are scheme isomorphisms obtained from pullback pasting,
with explicit projection formulas.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)

/-- Pullback of the first product projection over a rational point is the second factor. -/
def productFirstPointFibreIso (h : H.points) :
    (pullback (pullback.fst H.toSpec X.toSpec) h.val : Scheme) ≅ X.scheme :=
  pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso H.toSpec X.toSpec h.val ≪≫
    pullback.congrHom h.property rfl ≪≫ asIso (pullback.snd (𝟙 _) X.toSpec)

/-- The first-product fibre isomorphism is the second projection of the product. -/
theorem productFirstPointFibreIso_hom (h : H.points) :
    (productFirstPointFibreIso H X h).hom =
      pullback.fst (pullback.fst H.toSpec X.toSpec) h.val ≫
        pullback.snd H.toSpec X.toSpec := by
  simp [productFirstPointFibreIso]

/-- Pullback of the second product projection over a rational point is the first factor. -/
def productSecondPointFibreIso (x : X.points) :
    (pullback (pullback.snd H.toSpec X.toSpec) x.val : Scheme) ≅ H.scheme :=
  pullbackLeftPullbackSndIso H.toSpec X.toSpec x.val ≪≫
    pullback.congrHom rfl x.property ≪≫ asIso (pullback.fst H.toSpec (𝟙 _))

/-- The second-product fibre isomorphism is the first projection of the product. -/
theorem productSecondPointFibreIso_hom (x : X.points) :
    (productSecondPointFibreIso H X x).hom =
      pullback.fst (pullback.snd H.toSpec X.toSpec) x.val ≫
        pullback.fst H.toSpec X.toSpec := by
  simp [productSecondPointFibreIso]

variable [IsAlgClosed K] [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The scheme-theoretic fibre of the first product projection at a rational point
is homeomorphic to the second factor. -/
def productFirstFibreHomeomorph (h : H.points) :
    (CartesianMonoidalCategory.fst H.toOver X.toOver).left.fiber (H.pointMap h) ≃ₜ X.scheme :=
  (pointPullbackHomeomorph (Y := productVariety H X)
    (CartesianMonoidalCategory.fst H.toOver X.toOver) h).symm.trans
      (productFirstPointFibreIso H X h).hom.homeomorph

/-- The scheme-theoretic fibre of the second product projection at a rational point
is homeomorphic to the first factor. -/
def productSecondFibreHomeomorph (x : X.points) :
    (CartesianMonoidalCategory.snd H.toOver X.toOver).left.fiber (X.pointMap x) ≃ₜ H.scheme :=
  (pointPullbackHomeomorph (Y := productVariety H X)
    (CartesianMonoidalCategory.snd H.toOver X.toOver) x).symm.trans
      (productSecondPointFibreIso H X x).hom.homeomorph

/-- The first-product fibre homeomorphism evaluates the second product coordinate. -/
theorem productFirstFibreHomeomorph_apply (h : H.points)
    (z : (CartesianMonoidalCategory.fst H.toOver X.toOver).left.fiber (H.pointMap h)) :
    productFirstFibreHomeomorph H X h z =
      (CartesianMonoidalCategory.snd H.toOver X.toOver).left
        ((CartesianMonoidalCategory.fst H.toOver X.toOver).left.fiberι (H.pointMap h) z) := by
  let e := pointPullbackHomeomorph (Y := productVariety H X)
    (CartesianMonoidalCategory.fst H.toOver X.toOver) h
  change (productFirstPointFibreIso H X h).hom (e.symm z) = _
  rw [productFirstPointFibreIso_hom]
  erw [Scheme.Hom.comp_apply]
  have hf := pointPullbackHomeomorph_fst
    (Y := productVariety H X) (CartesianMonoidalCategory.fst H.toOver X.toOver) h (e.symm z)
  have he : e (e.symm z) = z := e.apply_symm_apply z
  rw [he] at hf
  exact congrArg (pullback.snd H.toSpec X.toSpec) hf.symm

/-- The second-product fibre homeomorphism evaluates the first product coordinate. -/
theorem productSecondFibreHomeomorph_apply (x : X.points)
    (z : (CartesianMonoidalCategory.snd H.toOver X.toOver).left.fiber (X.pointMap x)) :
    productSecondFibreHomeomorph H X x z =
      (CartesianMonoidalCategory.fst H.toOver X.toOver).left
        ((CartesianMonoidalCategory.snd H.toOver X.toOver).left.fiberι (X.pointMap x) z) := by
  let e := pointPullbackHomeomorph (Y := productVariety H X)
    (CartesianMonoidalCategory.snd H.toOver X.toOver) x
  change (productSecondPointFibreIso H X x).hom (e.symm z) = _
  rw [productSecondPointFibreIso_hom]
  erw [Scheme.Hom.comp_apply]
  have hf := pointPullbackHomeomorph_fst
    (Y := productVariety H X) (CartesianMonoidalCategory.snd H.toOver X.toOver) x (e.symm z)
  have he : e (e.symm z) = z := e.apply_symm_apply z
  rw [he] at hf
  exact congrArg (pullback.fst H.toSpec X.toSpec) hf.symm

end

end GroupActions.Variety
