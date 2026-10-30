import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteAffineRefinements

/-! # Matching coframes on a finite affine preimage cover

A quasi-compact scheme mapping to a matching model has a finite affine cover
refining its singleton charts. Every character power retains the chart maps
and the coframes of the same matching module.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem refinement_triangle {X Y : Scheme.{u}} (j : X ⟶ Y)
    (W : Y.OpenCover.{u}) (V : X.OpenCover.{u}) (e : V ⟶ W.pullback₁ j)
    (l : V.I₀) :
    (e.h₀ l ≫ W.pullbackHom j (e.s₀ l)) ≫ W.f (e.s₀ l) = V.f l ≫ j := by
  calc
    _ = e.h₀ l ≫ (W.pullbackHom j (e.s₀ l) ≫ W.f (e.s₀ l)) :=
      Category.assoc _ _ _
    _ = e.h₀ l ≫ ((W.pullback₁ j).f (e.s₀ l) ≫ j) :=
      congrArg (fun a => e.h₀ l ≫ a) (W.pullbackHom_map j (e.s₀ l))
    _ = (e.h₀ l ≫ (W.pullback₁ j).f (e.s₀ l)) ≫ j :=
      (Category.assoc _ _ _).symm
    _ = V.f l ≫ j := congrArg (fun a => a ≫ j) (e.w₀ l)

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- The matching coframe pulled through a specified singleton-chart factorization. -/
def matchingPreimageFrame {X A : Scheme.{u}} (j : X ⟶ cN.pt.left)
    (v : A ⟶ X) (index : J)
    (b : A ⟶ Spec (.of (N.obj (singletonIndex index))))
    (h : b ≫ (cN.ι.app (op (singletonIndex index))).left = v ≫ j) (n : ℕ) :
    (Scheme.Modules.pullback v).obj
        ((Scheme.Modules.pullback j).obj (matchingModule N cN delta n)) ≅
      unitModule A :=
  (Scheme.Modules.pullbackComp v j).app (matchingModule N cN delta n) ≪≫
    frame_on_composite b (cN.ι.app (op (singletonIndex index))).left
      (v ≫ j) h.symm (matchingModule N cN delta n)
      (localCharacterTrivialization N cN hcN delta n hco hn (singletonIndex index)
        index (Finset.mem_singleton_self index))

/-- A finite affine refinement of a preimage retains the singleton maps and all
power coframes of the original matching module. -/
theorem exists_matching_preimage_cover {X : Scheme.{u}} [CompactSpace X]
    (j : X ⟶ cN.pt.left) :
    ∃ (V : X.OpenCover.{u}) (_ : Finite V.I₀) (_ : ∀ l, IsAffine (V.X l))
      (index : V.I₀ → J)
      (b : ∀ l, V.X l ⟶ Spec (.of (N.obj (singletonIndex (index l)))))
      (h : ∀ l, b l ≫ (cN.ι.app (op (singletonIndex (index l)))).left = V.f l ≫ j)
      (E : ∀ n l, (Scheme.Modules.pullback (V.f l)).obj
        ((Scheme.Modules.pullback j).obj (matchingModule N cN delta n)) ≅
          unitModule (V.X l)),
      ∀ n l, E n l = matchingPreimageFrame N cN hcN delta hco hn
        j (V.f l) (index l) (b l) (h l) n := by
  let W := matchingSingletonCover N cN hcN
  obtain ⟨V, hfinite, haffine, ⟨e⟩⟩ := exists_affine_cover_refinement (W.pullback₁ j)
  let b (l : V.I₀) := e.h₀ l ≫ W.pullbackHom j (e.s₀ l)
  have h (l : V.I₀) : b l ≫ (cN.ι.app (op (singletonIndex (e.s₀ l)))).left =
      V.f l ≫ j := refinement_triangle j W V e l
  exact ⟨V, hfinite, haffine, e.s₀, b, h,
    fun n l => matchingPreimageFrame N cN hcN delta hco hn j (V.f l)
      (e.s₀ l) (b l) (h l) n, fun _ _ => rfl⟩

end SchubertGeometry.RetainedCharacter
