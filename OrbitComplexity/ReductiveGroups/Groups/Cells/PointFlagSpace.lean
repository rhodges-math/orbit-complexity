import OrbitComplexity.ReductiveGroups.Algebra.PointZariski
import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Point Flag Space

The Zariski topology on the `K`-points of an affine group and the coset
space of a subgroup of points with its quotient topology.

For an affine group `Spec B` over a field `K`, the `K`-points carry the
Zariski topology induced from `Spec B` (closed sets are common zero loci of
coordinate functions). Left and right translations are continuous, since
they are composition with the translation algebra maps. For a subgroup `H`
of points, `G(K) ⧸ H` carries the quotient topology, the quotient map is
open, and the closure of an image is the image of the closure of the
saturation. For `H` the K-points of a Borel subgroup this is the closed-point
space of the flag variety with its Zariski topology. -/

noncomputable section
namespace ReductiveGroups

open TauCeti Topology Pointwise

universe u v
variable {K : Type u} {B : Type v} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The Zariski topology on the `K`-points of the affine group `Spec B`,
induced from `Spec B` through kernels. -/
instance pointGroupZariskiTopology : TopologicalSpace (WithConv (B →ₐ[K] K)) :=
  TopologicalSpace.induced WithConv.ofConv pointZariskiTopology

/-- Closed sets of points are exactly common zero loci of coordinate
functions. -/
theorem pointGroup_isClosed_iff (s : Set (WithConv (B →ₐ[K] K))) :
    IsClosed s ↔ ∃ S : Set B, s = {g | ∀ f ∈ S, g.ofConv f = 0} := by
  let _ : TopologicalSpace (B →ₐ[K] K) := pointZariskiTopology
  change IsClosed[TopologicalSpace.induced WithConv.ofConv pointZariskiTopology] s ↔ _
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨S, rfl⟩ := (pointZariski_isClosed_iff t).mp ht
    exact ⟨S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨pointZeroLocus K S, pointZariski_isClosed_zeroLocus S, rfl⟩

/-- Pullback by left translation by a `K`-point. -/
noncomputable def leftTranslationAlgHom (g : WithConv (B →ₐ[K] K)) : B →ₐ[K] B :=
  (WithConv.toConv ((Algebra.ofId K B).comp g.ofConv) *
    WithConv.toConv (AlgHom.id K B)).ofConv

/-- Composing a point with left translation is convolution on the left. -/
theorem toConv_comp_leftTranslationAlgHom (f g : WithConv (B →ₐ[K] K)) :
    WithConv.toConv (f.ofConv.comp (leftTranslationAlgHom g)) = g * f := by
  apply WithConv.ofConv_injective
  ext x
  change f.ofConv (leftTranslationAlgHom g x) = (g * f).ofConv x
  rw [leftTranslationAlgHom, AlgHom.convMul_apply, AlgHom.convMul_apply]
  induction Coalgebra.comul (R := K) x using TensorProduct.inductionOn with
  | add y z hy hz => simp [hy, hz]
  | tmul y z => simp

private theorem continuous_comp_algHom (ψ : B →ₐ[K] B) :
    Continuous (fun f : WithConv (B →ₐ[K] K) => WithConv.toConv (f.ofConv.comp ψ)) := by
  let _ : TopologicalSpace (B →ₐ[K] K) := pointZariskiTopology
  apply continuous_induced_rng.mpr
  exact (pointZariski_continuous_comp ψ).comp continuous_induced_dom

/-- Left and right translations of points are continuous. -/
instance pointGroup_separatelyContinuousMul :
    SeparatelyContinuousMul (WithConv (B →ₐ[K] K)) where
  continuous_const_mul {g} := by
    have h := continuous_comp_algHom (K := K) (leftTranslationAlgHom g)
    simpa only [toConv_comp_leftTranslationAlgHom] using h
  continuous_mul_const {g} := by
    have h := continuous_comp_algHom (K := K) (TauCeti.HopfAlgebra.rightTranslationAlgHom g)
    simpa only [TauCeti.HopfAlgebra.toConv_comp_rightTranslationAlgHom] using h

/-- In the coset space of a subgroup of points, the closure of the image of a
set is the image of the closure of its right saturation. -/
theorem closure_image_mk_eq (H : Subgroup (WithConv (B →ₐ[K] K)))
    (s : Set (WithConv (B →ₐ[K] K))) :
    closure ((QuotientGroup.mk : WithConv (B →ₐ[K] K) → WithConv (B →ₐ[K] K) ⧸ H) '' s) =
      QuotientGroup.mk '' closure (s * (H : Set (WithConv (B →ₐ[K] K)))) := by
  have hopen := QuotientGroup.isOpenMap_coe (N := H)
  have hcont : Continuous (QuotientGroup.mk :
      WithConv (B →ₐ[K] K) → WithConv (B →ₐ[K] K) ⧸ H) := continuous_quot_mk
  rw [← QuotientGroup.preimage_image_mk_eq_mul, ← hopen.preimage_closure_eq_closure_preimage hcont,
    Set.image_preimage_eq _ QuotientGroup.mk_surjective]

end ReductiveGroups
