import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Functor.Category

/-! # sum-ideal quotients of the chosen target diagrams -/

noncomputable section
open CategoryTheory

namespace FrobeniusSplitting

universe u v w

variable {S : Type u} [CommRing S] {C : Type v} [Category.{w} C]
  (F B O : C ⥤ CommAlgCat.{u} S) (β : F ⟶ B) (γ : F ⟶ O)

private theorem kernel_stable {i j : C} (a : i ⟶ j) :
    RingHom.ker (β.app i).hom.toRingHom ≤
      (RingHom.ker (β.app j).hom.toRingHom).comap (F.map a).hom.toRingHom := by
  intro x hx
  change (β.app j).hom ((F.map a).hom x) = 0
  have hn : (β.app j).hom ((F.map a).hom x) =
      (B.map a).hom ((β.app i).hom x) :=
    congrArg (fun f => f.hom x) (β.naturality a)
  have hx' : (β.app i).hom x = 0 := RingHom.mem_ker.mp hx
  rw [hx', map_zero] at hn
  exact hn

private theorem sum_stable {i j : C} (a : i ⟶ j) :
    RingHom.ker (β.app i).hom.toRingHom ⊔ RingHom.ker (γ.app i).hom.toRingHom ≤
      (RingHom.ker (β.app j).hom.toRingHom ⊔
        RingHom.ker (γ.app j).hom.toRingHom).comap (F.map a).hom.toRingHom := by
  apply sup_le
  · exact (kernel_stable F B β a).trans (Ideal.comap_mono le_sup_left)
  · exact (kernel_stable F O γ a).trans (Ideal.comap_mono le_sup_right)

/-- The chosen ambient diagram quotiented by the sums of the two
quotient-map kernels. Its arrows are induced by the original restriction maps. -/
def sumKernelDiagram : C ⥤ CommAlgCat.{u} S where
  obj i := CommAlgCat.of S (F.obj i ⧸
    (RingHom.ker (β.app i).hom.toRingHom ⊔ RingHom.ker (γ.app i).hom.toRingHom))
  map a := CommAlgCat.ofHom (Ideal.quotientMapₐ _ (F.map a).hom (sum_stable F B O β γ a))
  map_id i := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk _ ((F.map (𝟙 i)).hom x) = Ideal.Quotient.mk _ x
    rw [F.map_id]
    rfl
  map_comp a b := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk _ ((F.map (a ≫ b)).hom x) =
      Ideal.Quotient.mk _ ((F.map b).hom ((F.map a).hom x))
    rw [F.map_comp]
    rfl

/-- The canonical quotient from the same ambient coefficient diagram is
natural on every original restriction arrow. -/
def sumKernelQuotient : F ⟶ sumKernelDiagram F B O β γ where
  app i := CommAlgCat.ofHom (Ideal.Quotient.mkₐ S _)
  naturality _ _ a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

/-- Every component is surjective and its kernel is exactly the sum,
without a flatness or reducedness requirement on any chosen coefficient node. -/
theorem sumKernelQuotient_ker (i : C) :
    Function.Surjective ((sumKernelQuotient F B O β γ).app i).hom ∧
      RingHom.ker ((sumKernelQuotient F B O β γ).app i).hom.toRingHom =
        RingHom.ker (β.app i).hom.toRingHom ⊔ RingHom.ker (γ.app i).hom.toRingHom := by
  exact ⟨Ideal.Quotient.mkₐ_surjective S _, Ideal.Quotient.mkₐ_ker S _⟩


end FrobeniusSplitting
