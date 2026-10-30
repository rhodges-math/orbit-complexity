import OrbitComplexity.ReductiveGroups.Groups.Cells.PointFlagSpace
import TauCeti.RingTheory.FiniteType.PointSeparation

/-! # Affine translations

Translations on a reduced affine group of finite type are coordinate algebra equivalences.

## Main definitions

* `GroupActions.leftTranslationAlgEquiv`: the coordinate equivalence for left translation.
-/

namespace GroupActions

noncomputable section

universe u v

variable {K : Type u} [Field K] {A : Type v} [CommRing A] [HopfAlgebra K A]

/-- The counit after left translation evaluates at the translating point. -/
@[simp]
theorem counit_comp_leftTranslation (g : WithConv (A →ₐ[K] K)) :
    (Bialgebra.counitAlgHom K A).comp (ReductiveGroups.leftTranslationAlgHom g) =
      g.ofConv := by
  rw [ReductiveGroups.leftTranslationAlgHom, AlgHom.comp_convMul_distrib]
  have hcounit : (Bialgebra.counitAlgHom K A).comp (AlgHom.id K A) =
      Bialgebra.counitAlgHom K A := AlgHom.comp_id _
  have hpoint : (Bialgebra.counitAlgHom K A).comp
      ((Algebra.ofId K A).comp g.ofConv) = g.ofConv := by
    ext x
    simp
  rw [hpoint, hcounit]
  change (g * 1).ofConv = g.ofConv
  rw [mul_one]

variable [IsAlgClosed K] [Algebra.FiniteType K A] [IsReduced A]

/-- Composing two left-translation coordinate maps reverses the order of their group points. -/
theorem leftTranslationAlgHom_comp (f g : WithConv (A →ₐ[K] K)) :
    (ReductiveGroups.leftTranslationAlgHom f).comp
        (ReductiveGroups.leftTranslationAlgHom g) =
      ReductiveGroups.leftTranslationAlgHom (g * f) := by
  ext a
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro p
  have hp : WithConv.toConv (p.comp ((ReductiveGroups.leftTranslationAlgHom f).comp
        (ReductiveGroups.leftTranslationAlgHom g))) =
      WithConv.toConv (p.comp (ReductiveGroups.leftTranslationAlgHom (g * f))) := by
    change WithConv.toConv ((p.comp (ReductiveGroups.leftTranslationAlgHom f)).comp
      (ReductiveGroups.leftTranslationAlgHom g)) = _
    rw [ReductiveGroups.toConv_comp_leftTranslationAlgHom,
      ReductiveGroups.toConv_comp_leftTranslationAlgHom,
      ReductiveGroups.toConv_comp_leftTranslationAlgHom, mul_assoc]
  exact DFunLike.congr_fun (congrArg WithConv.ofConv hp) a

/-- The identity point gives the identity left-translation coordinate map. -/
@[simp]
theorem leftTranslationAlgHom_one :
    ReductiveGroups.leftTranslationAlgHom (1 : WithConv (A →ₐ[K] K)) = AlgHom.id K A := by
  ext a
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro p
  have hp := ReductiveGroups.toConv_comp_leftTranslationAlgHom
    (WithConv.toConv p) (1 : WithConv (A →ₐ[K] K))
  rw [one_mul] at hp
  exact DFunLike.congr_fun (congrArg WithConv.ofConv hp) a

/-- Left translation is an equivalence of the reduced affine group's coordinate algebra. -/
def leftTranslationAlgEquiv (g : WithConv (A →ₐ[K] K)) : A ≃ₐ[K] A :=
  AlgEquiv.ofAlgHom (ReductiveGroups.leftTranslationAlgHom g)
    (ReductiveGroups.leftTranslationAlgHom g⁻¹)
    (by rw [leftTranslationAlgHom_comp, inv_mul_cancel, leftTranslationAlgHom_one])
    (by rw [leftTranslationAlgHom_comp, mul_inv_cancel, leftTranslationAlgHom_one])

/-- The left-translation equivalence has the coordinate map of left translation. -/
theorem leftTranslationAlgEquiv_toAlgHom (g : WithConv (A →ₐ[K] K)) :
    (leftTranslationAlgEquiv g).toAlgHom = ReductiveGroups.leftTranslationAlgHom g := rfl


end

end GroupActions
