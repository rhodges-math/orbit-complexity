import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordFaceKernels
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Subword faces and omitted-letter ideals -/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry

open private priorIndex lastIndex lastSection lastSection_closed lastSection_endpoint
  familyCast erase_append_before erase_append_last bsdhOmitMap_last closed_of_cartesian from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
open private ker_of_pullback from
  OrbitComplexity.SchubertGeometry.Normality.Richardson.RichardsonCoordinateKernel

private theorem cast_kernel {I : Type*} (F : I → Scheme.{u})
    {a b : I} (h : a = b) {Y : Scheme.{u}} (g : F b ⟶ Y) :
    (familyCast F h ≫ g).ker = g.ker := by
  let : IsIso (familyCast F h) := by
    dsimp only [familyCast]
    infer_instance
  exact Scheme.Hom.ker_comp_of_isIso (familyCast F h) g

private theorem sup_insert_of_eq {L I : Type*} [SemilatticeSup L] [OrderBot L]
    [DecidableEq I]
    (F : Finset I) (J : I → L) (j : I) {A B C : L}
    (hA : A = B ⊔ C) (hB : B = F.sup J) (hC : C = J j) :
    A = (insert j F).sup J := by
  classical
  rw [hA, hB, hC, Finset.sup_insert]
  exact sup_comm _ _

private theorem sup_comap {X Y : Scheme.{u}} {I : Type*}
    (F : Finset I) (J : I → Y.IdealSheafData) (f : X ⟶ Y) :
    (F.sup J).comap f = F.sup (fun k => (J k).comap f) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, Scheme.IdealSheafData.comap_bot]
  | @insert k F _hk ih =>
    simp only [Finset.sup_insert, Scheme.IdealSheafData.comap_sup, ih]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

private theorem mapped_kernel (w : List G.rootBase.support) (i : G.rootBase.support)
    (F : Finset (Fin w.length)) :
    (F.sup (fun k => (bsdhOmitMap G w k).ker)).comap (bsdhAppendFst G w i) =
      (F.image (priorIndex G w i)).sup
        (fun k => (bsdhOmitMap G (w ++ [i]) k).ker) := by
  classical
  rw [sup_comap, Finset.sup_image]
  apply Finset.sup_congr rfl
  intro k _
  let : IsClosedImmersion (bsdhOmitMap G w k) := bsdhOmitMap_closed G w k
  exact (ker_of_pullback (bsdhOmitMap G w k)
    (bsdhOmitMap G (w ++ [i]) (priorIndex G w i k))
    (familyCast (bsdhScheme G) (erase_append_before w i k.val k.isLt) ≫
      bsdhAppendFst G (w.eraseIdx k.val) i)
    (bsdhAppendFst G w i) (bsdhOmitMap_cartesian G w i k)).symm

private theorem last_kernel (w : List G.rootBase.support) (i : G.rootBase.support) :
    (bsdhOmitMap G (w ++ [i]) (lastIndex G w i)).ker =
      (lastSection G w i).ker := by
  exact (congrArg Scheme.Hom.ker (bsdhOmitMap_last G w i)).trans
    (cast_kernel (bsdhScheme G) (erase_append_last w i) (lastSection G w i))

private def SubwordKernel (v w : List G.rootBase.support) : Prop :=
  ∃ (a : bsdhScheme G v ⟶ bsdhScheme G w) (F : Finset (Fin w.length)),
    IsClosedImmersion a ∧ a ≫ bsdhMap G w = bsdhMap G v ∧
      a.ker = F.sup (fun k => (bsdhOmitMap G w k).ker)

private theorem empty_face : SubwordKernel G [] [] := by
  refine ⟨𝟙 (bsdhScheme G []), ∅, inferInstance, Category.id_comp _, ?_⟩
  simp only [Finset.sup_empty, Scheme.Hom.ker_eq_bot_of_isIso]

private theorem keep_face {v w : List G.rootBase.support}
    (h : SubwordKernel G v w) (i : G.rootBase.support) :
    SubwordKernel G (v ++ [i]) (w ++ [i]) := by
  classical
  obtain ⟨a, F, ha, he, hk⟩ := h
  let : IsClosedImmersion a := ha
  let b := bsdhAppendMap G a he i
  let : IsClosedImmersion b :=
    closed_of_cartesian _ _ _ _ (bsdhAppendMap_cartesian G a he i)
  refine ⟨b, F.image (priorIndex G w i), inferInstance,
    bsdhAppendMap_endpoint G a he i, ?_⟩
  calc
    b.ker = a.ker.comap (bsdhAppendFst G w i) := bsdhAppendMap_kernel G a he i
    _ = (F.sup (fun k => (bsdhOmitMap G w k).ker)).comap
        (bsdhAppendFst G w i) := congrArg (fun J => J.comap (bsdhAppendFst G w i)) hk
    _ = _ := mapped_kernel G w i F

private theorem omit_face {v w : List G.rootBase.support}
    (h : SubwordKernel G v w) (i : G.rootBase.support) :
    SubwordKernel G v (w ++ [i]) := by
  classical
  obtain ⟨a, F, ha, he, hk⟩ := h
  let : IsClosedImmersion a := ha
  let : IsClosedImmersion (lastSection G w i) := lastSection_closed G w i
  let b := a ≫ lastSection G w i
  refine ⟨b, insert (lastIndex G w i) (F.image (priorIndex G w i)), inferInstance,
    ?_, ?_⟩
  · calc
      b ≫ bsdhMap G (w ++ [i]) = a ≫ (lastSection G w i ≫
          bsdhMap G (w ++ [i])) := Category.assoc _ _ _
      _ = a ≫ bsdhMap G w := by rw [lastSection_endpoint G w i]
      _ = _ := he
  · have hm : (bsdhAppendMap G a he i).ker =
        (F.image (priorIndex G w i)).sup
          (fun k => (bsdhOmitMap G (w ++ [i]) k).ker) :=
      (bsdhAppendMap_kernel G a he i).trans
        ((congrArg (fun J => J.comap (bsdhAppendFst G w i)) hk).trans
          (mapped_kernel G w i F))
    exact sup_insert_of_eq (F.image (priorIndex G w i))
      (fun k => (bsdhOmitMap G (w ++ [i]) k).ker) (lastIndex G w i)
      (bsdh_section_kernel G a he i) hm (last_kernel G w i).symm

private theorem reverse_face {v w : List G.rootBase.support} (h : v.Sublist w) :
    SubwordKernel G v.reverse w.reverse := by
  induction h with
  | slnil => exact empty_face G
  | cons i h ih => simpa only [List.reverse_cons] using omit_face G ih i
  | cons_cons i h ih => simpa only [List.reverse_cons] using keep_face G ih i

/-- Every subword has a closed, endpoint-preserving BSDH face whose scheme
ideal is the finite sum of its omitted-letter boundary ideals. -/
theorem bsdh_subword_face {v w : List G.rootBase.support} (h : v.Sublist w) :
    ∃ (a : bsdhScheme G v ⟶ bsdhScheme G w) (F : Finset (Fin w.length)),
      IsClosedImmersion a ∧ a ≫ bsdhMap G w = bsdhMap G v ∧
        a.ker = F.sup (fun k => (bsdhOmitMap G w k).ker) := by
  change SubwordKernel G v w
  simpa only [List.reverse_reverse] using reverse_face G h.reverse

end SchubertGeometry
