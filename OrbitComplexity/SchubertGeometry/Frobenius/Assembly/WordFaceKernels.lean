import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
import OrbitComplexity.SchubertGeometry.Normality.Richardson.RichardsonCoordinateKernel
import OrbitComplexity.FrobeniusSplitting.Normality.Images.ClosedIntersectionKernel
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Kernels of subword faces under append -/

set_option autoImplicit false
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry

open private lastSection lastSection_closed lastSection_fst closed_of_cartesian from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
open private ker_of_pullback from
  OrbitComplexity.SchubertGeometry.Normality.Richardson.RichardsonCoordinateKernel

private theorem section_pullback {D : Type u} [Category.{v} D]
    {X Y B E : D} (π : Y ⟶ X) (δ : X ⟶ Y) (hδ : δ ≫ π = 𝟙 X)
    (d : B ⟶ X) (e : E ⟶ Y) (q : E ⟶ B) (h : IsPullback e q π d) :
    ∃ t : B ⟶ E, IsPullback d t δ e := by
  let t : B ⟶ E := h.lift (d ≫ δ) (𝟙 B)
    (by simp only [Category.assoc, hδ, Category.comp_id, Category.id_comp])
  have ht : t ≫ e = d ≫ δ := h.lift_fst _ _ _
  have hq : t ≫ q = 𝟙 B := h.lift_snd _ _ _
  have ho : IsPullback d (t ≫ q) (δ ≫ π) d := by
    rw [hq, hδ]
    exact IsPullback.of_vert_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
  exact ⟨t, ho.of_bot ht.symm h⟩

private theorem section_kernel {X Y B E : Scheme.{u}}
    (π : Y ⟶ X) (δ : X ⟶ Y) (hδ : δ ≫ π = 𝟙 X)
    (d : B ⟶ X) (e : E ⟶ Y) (q : E ⟶ B) (h : IsPullback e q π d)
    [IsClosedImmersion δ] [IsClosedImmersion e] :
    (d ≫ δ).ker = e.ker ⊔ δ.ker := by
  obtain ⟨t, ht⟩ := section_pullback π δ hδ d e q h
  calc
    (d ≫ δ).ker = ((ht.isoPullback.hom ≫ pullback.fst δ e) ≫ δ).ker := by
      rw [ht.isoPullback_hom_fst]
    _ = (ht.isoPullback.hom ≫ (pullback.fst δ e ≫ δ)).ker := by
      rw [Category.assoc]
    _ = (pullback.fst δ e ≫ δ).ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = δ.ker ⊔ e.ker := FrobeniusSplitting.closed_intersection_ker δ e
    _ = _ := sup_comm _ _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- Appending a letter pulls a closed subword face ideal back along the
last projective-bundle projection. -/
theorem bsdhAppendMap_kernel {v w : List G.rootBase.support}
    (a : bsdhScheme G v ⟶ bsdhScheme G w)
    (ha : a ≫ bsdhMap G w = bsdhMap G v) [IsClosedImmersion a]
    (i : G.rootBase.support) :
    (bsdhAppendMap G a ha i).ker = a.ker.comap (bsdhAppendFst G w i) :=
  ker_of_pullback a (bsdhAppendMap G a ha i) (bsdhAppendFst G v i)
    (bsdhAppendFst G w i) (bsdhAppendMap_cartesian G a ha i)

/-- Omitting the last letter intersects the appended prior face with the
last boundary, with equality of their scheme ideals. -/
theorem bsdh_section_kernel {v w : List G.rootBase.support}
    (a : bsdhScheme G v ⟶ bsdhScheme G w)
    (ha : a ≫ bsdhMap G w = bsdhMap G v) [IsClosedImmersion a]
    (i : G.rootBase.support) :
    (a ≫ lastSection G w i).ker =
      (bsdhAppendMap G a ha i).ker ⊔ (lastSection G w i).ker := by
  let : IsClosedImmersion (bsdhAppendMap G a ha i) :=
    closed_of_cartesian _ _ _ _ (bsdhAppendMap_cartesian G a ha i)
  let : IsClosedImmersion (lastSection G w i) := lastSection_closed G w i
  exact section_kernel (bsdhAppendFst G w i) (lastSection G w i)
    (lastSection_fst G w i) a (bsdhAppendMap G a ha i)
    (bsdhAppendFst G v i) (bsdhAppendMap_cartesian G a ha i)

end SchubertGeometry
