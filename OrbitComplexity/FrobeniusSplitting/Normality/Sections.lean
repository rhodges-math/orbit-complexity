import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Integral closedness of regular functions

An element of the function field that is integral over the global regular functions
belongs to every normal stalk. Representatives on open neighborhoods agree in the
function field and glue to a global regular function.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

private instance nonempty_top (X : Scheme) [IsIntegral X] :
    Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

private theorem field_res {X : Scheme} [IsIntegral X] {U V : X.Opens}
    [Nonempty U] [Nonempty V] (h : V ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op s) =
      X.germToFunctionField U s := by
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ s

/-- Global regular functions on an integral scheme with normal local rings are
integrally closed in its function field. -/
theorem isIntegrallyClosedIn_functionField {X : Scheme} [IsIntegral X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosedIn Γ(X, ⊤) X.functionField := by
  refine isIntegrallyClosedIn_iff.mpr ⟨X.germToFunctionField_injective ⊤, ?_⟩
  intro r hr
  have hlocal (x : X) : ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.germ U x hx s) = r := by
    have := hn x
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf
      ⟨x, show x ∈ (⊤ : X.Opens) from trivial⟩
    have := functionField_isScalarTower X ⊤
      ⟨x, show x ∈ (⊤ : X.Opens) from trivial⟩
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (hr.tower_top (A := X.presheaf.stalk x))
    obtain ⟨U, hx, s, hs⟩ := X.presheaf.exists_germ_eq t
    exact ⟨U, hx, s, by rwa [hs]⟩
  choose U hx s hs using hlocal
  have (x : X) : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  have hfield (x : X) : X.germToFunctionField (U x) (s x) = r := by
    simpa only [Scheme.algebraMap_germ_eq_germToFunctionField] using hs x
  have hgen (x : X) : genericPoint X ∈ U x :=
    ((genericPoint_spec X).mem_open_set_iff (U x).isOpen).mpr (by
      exact ⟨x, trivial, hx x⟩)
  have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro i j
    have hnon : Nonempty (show X.Opens from U i ⊓ U j) :=
      ⟨⟨genericPoint X, hgen i, hgen j⟩⟩
    apply @Scheme.germToFunctionField_injective X _ (U i ⊓ U j) hnon
    exact (field_res inf_le_left (s i)).trans
      ((hfield i).trans ((hfield j).symm.trans (field_res inf_le_right (s j)).symm))
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨glued, hglued, -⟩ := X.sheaf.existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) hcover s hcompatible
  refine ⟨glued, ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  change X.germToFunctionField ⊤ glued = r
  have hgluex : X.presheaf.map (homOfLE (show U x ≤ ⊤ from le_top)).op glued = s x :=
    hglued x
  exact (field_res le_top glued).symm.trans
    ((congrArg (X.germToFunctionField (U x)) hgluex).trans (hfield x))

end FrobeniusSplitting
