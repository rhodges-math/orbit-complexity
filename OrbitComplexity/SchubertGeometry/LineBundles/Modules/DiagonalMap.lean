import OrbitComplexity.SchubertGeometry.LineBundles.Modules.ModuleLocality
import Mathlib.CategoryTheory.Abelian.Basic

/-! # Extending a sheaf map through an epimorphism and a monomorphism -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory CategoryTheory.Limits
universe v u

/-- A commuting epi-mono square has a unique diagonal in an abelian category. -/
theorem epiMono_diagonal {C : Type u} [Category.{v} C] [Abelian C]
    {E M N P : C} (e : E ⟶ M) [Epi e] (i : N ⟶ P) [Mono i]
    (g : E ⟶ N) (q : M ⟶ P) (h : e ≫ q = g ≫ i) :
    ∃! d : M ⟶ N, e ≫ d = g ∧ d ≫ i = q := by
  have hg : kernel.ι e ≫ g = 0 := by
    apply (cancel_mono i).mp
    calc
      _ = kernel.ι e ≫ (g ≫ i) := Category.assoc _ _ _
      _ = kernel.ι e ≫ (e ≫ q) := by rw [h]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
      _ = _ := zero_comp.symm
  let d := Abelian.epiDesc e g hg
  have hd : e ≫ d = g := Abelian.comp_epiDesc e g hg
  have hi : d ≫ i = q := by
    apply (cancel_epi e).mp
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ i) hd).trans h.symm)
  refine ⟨d, ⟨hd, hi⟩, ?_⟩
  intro d' hd'
  exact (cancel_epi e).mp (hd'.1.trans hd.symm)

end SchubertGeometry.ProjectiveLine
