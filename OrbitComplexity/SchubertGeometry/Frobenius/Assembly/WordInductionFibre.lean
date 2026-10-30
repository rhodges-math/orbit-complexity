import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The prior model on an append field fibre

The three coefficient extensions carry the chosen prior cocone to the
append field diagram. Their Cartesian projections compose, and each affine
leg remains the original prior leg after the canonical coefficient map.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

open private AppendChartData AppendChartData.N from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
open private stageRings terminalRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
open private fieldRings scalarCoefficients from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordSplitting

namespace SchubertGeometry.RetainedCharacter

private theorem spec_three {A B C D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    Spec.map (f ≫ g ≫ h) = Spec.map h ≫ Spec.map g ≫ Spec.map f := by
  calc
    _ = Spec.map (g ≫ h) ≫ Spec.map f := Spec.map_comp f (g ≫ h)
    _ = (Spec.map h ≫ Spec.map g) ≫ Spec.map f :=
      congrArg (fun a => a ≫ Spec.map f) (Spec.map_comp g h)
    _ = _ := Category.assoc _ _ _

private theorem three_legs {D : Type v} [Category D]
    {A₀ A₁ A₂ A₃ X₀ X₁ X₂ X₃ : D}
    (l₀ : A₀ ⟶ X₀) (l₁ : A₁ ⟶ X₁) (l₂ : A₂ ⟶ X₂) (l₃ : A₃ ⟶ X₃)
    (e₀ : A₁ ⟶ A₀) (e₁ : A₂ ⟶ A₁) (e₂ : A₃ ⟶ A₂)
    (q₀ : X₁ ⟶ X₀) (q₁ : X₂ ⟶ X₁) (q₂ : X₃ ⟶ X₂)
    (h₀ : l₁ ≫ q₀ = e₀ ≫ l₀) (h₁ : l₂ ≫ q₁ = e₁ ≫ l₁)
    (h₂ : l₃ ≫ q₂ = e₂ ≫ l₂) :
    l₃ ≫ (q₂ ≫ q₁ ≫ q₀) = (e₂ ≫ e₁ ≫ e₀) ≫ l₀ := by
  calc
    _ = (l₃ ≫ q₂) ≫ (q₁ ≫ q₀) := (Category.assoc _ _ _).symm
    _ = (e₂ ≫ l₂) ≫ (q₁ ≫ q₀) := congrArg (fun f => f ≫ (q₁ ≫ q₀)) h₂
    _ = e₂ ≫ ((l₂ ≫ q₁) ≫ q₀) := by simp only [Category.assoc]
    _ = e₂ ≫ ((e₁ ≫ l₁) ≫ q₀) := congrArg (fun f => e₂ ≫ (f ≫ q₀)) h₁
    _ = e₂ ≫ e₁ ≫ (l₁ ≫ q₀) := by simp only [Category.assoc]
    _ = e₂ ≫ e₁ ≫ (e₀ ≫ l₀) := congrArg (fun f => e₂ ≫ e₁ ≫ f) h₀
    _ = _ := by simp only [Category.assoc]

/-- The canonical append field diagram, its colimit and its Cartesian
projection to the carried prior model. -/
structure AppendPriorFibre {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    {L : NextLetter M i} (g : AppendGeometry M L)
    (T κ : Type u) [tComm : CommRing T] [κComm : CommRing κ]
    [sTAlg : Algebra g.pre.S T] [tκAlg : Algebra T κ] where
  /-- Open transition morphisms of the field diagram. -/
  nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
        g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
        g.prior) T κ tComm κComm sTAlg tκAlg).map f).hom.toRingHom))
  /-- Local directedness of the field diagram. -/
  nDir : ((((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T κ
      tComm κComm sTAlg tκAlg).op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
    Scheme.forget).IsLocallyDirected)
  /-- The field-fibre cocone of the prior model. -/
  cPrior : Cocone ((@fieldRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
      (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T κ
      tComm κComm sTAlg tκAlg).op ⋙ algSpec (.of κ))
  /-- The colimit certificate of the field cocone. -/
  hcPrior : IsColimit cPrior
  /-- The projection to the carried prior model. -/
  q : cPrior.pt.left ⟶ g.prior.cT.pt.left
  /-- The composite coefficient-extension Cartesian square. -/
  hq : IsPullback q cPrior.pt.hom g.prior.cT.pt.hom
    (Spec.map (CommRingCat.ofHom (algebraMap T κ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap g.pre.S T)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion g.hTpre).toRingHom))
  /-- The affine legs of the projection are the canonical coefficient maps. -/
  hleg : ∀ s, (cPrior.ι.app (op s)).left ≫ q =
    Spec.map ((@scalarCoefficients.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
        (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior) T
        κ tComm κComm sTAlg tκAlg).app s) ≫ (g.prior.cT.ι.app (op s)).left

/-- Three successive scalar extensions construct the append prior field
cocone, preserving its Cartesian projection and all affine legs. -/
theorem exists_append_prior_fibre {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    {L : NextLetter M i} (g : AppendGeometry M L)
    (T κ : Type u) [tComm : CommRing T] [κComm : CommRing κ]
    [sTAlg : Algebra g.pre.S T] [tκAlg : Algebra T κ] :
    Nonempty (@AppendPriorFibre.{u} K kField kClosed kZero G word M i L
      g T κ tComm κComm sTAlg tκAlg) := by
  obtain ⟨hopenS, hdirS, cS, qS, ⟨hcS⟩, hqS, hlegS⟩ :=
    @exists_fixed_scalar_cocone.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
        (Category.{u} {s : Finset M.J // s.Nonempty})) (inferInstanceAs (Quiver.IsThin {s : Finset
        M.J // s.Nonempty})) (inferInstanceAs (Small.{u} {s : Finset M.J // s.Nonempty}))
      g.prior.T g.pre.S (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          g.prior.T) (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
      (Subalgebra.inclusion g.hTpre).toAlgebra (AppendChartData.N (@NextLetter.scalarCharts.{u} K
          kField kClosed kZero G word M i L g.coefficients g.prior))
      (fun {s t} f => @g.prior.prefix.nOpen t.unop s.unop f.unop)
      g.prior.prefix.nDir g.prior.cT g.prior.hcT
  obtain ⟨hopenT, hdirT, cT, qT, ⟨hcT⟩, hqT, hlegT⟩ :=
    @exists_fixed_scalar_cocone.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
        (Category.{u} {s : Finset M.J // s.Nonempty})) (inferInstanceAs (Quiver.IsThin {s : Finset
        M.J // s.Nonempty})) (inferInstanceAs (Small.{u} {s : Finset M.J // s.Nonempty}))
      g.pre.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          tComm sTAlg (@stageRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre
          (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients g.prior))
      hopenS hdirS cS hcS
  obtain ⟨hopenκ, hdirκ, cκ, qκ, ⟨hcκ⟩, hqκ, hlegκ⟩ :=
    @exists_fixed_scalar_cocone.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
        (Category.{u} {s : Finset M.J // s.Nonempty})) (inferInstanceAs (Quiver.IsThin {s : Finset
        M.J // s.Nonempty})) (inferInstanceAs (Small.{u} {s : Finset M.J // s.Nonempty}))
      T κ tComm κComm tκAlg (@terminalRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
          g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior) T tComm sTAlg)
      hopenT hdirT cT hcT
  refine ⟨{ nOpen := fun {s t} f => hopenκ f.op
            nDir := hdirκ
            cPrior := cκ
            hcPrior := hcκ
            q := qκ ≫ qT ≫ qS
            hq := ?_
            hleg := ?_ }⟩
  · simpa only [Category.assoc] using (hqκ.paste_horiz hqT).paste_horiz hqS
  · intro s
    have hs := three_legs
      (g.prior.cT.ι.app (op s)).left (cS.ι.app (op s)).left
      (cT.ι.app (op s)).left (cκ.ι.app (op s)).left
      (Spec.map ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset M.J // s.Nonempty})) g.prior.T g.pre.S (@Subalgebra.toCommRing ℤ
          K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
          (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (Subalgebra.inclusion g.hTpre).toAlgebra (AppendChartData.N (@NextLetter.scalarCharts.{u}
          K kField kClosed kZero G word M i L g.coefficients g.prior))).app s))
      (Spec.map ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset M.J // s.Nonempty})) g.pre.S T (@Subalgebra.toCommRing ℤ K
          Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing
          K (@Field.toDivisionRing K kField))) g.pre.S) tComm sTAlg (@stageRings.{u} K kField
          kClosed kZero g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField
          kClosed kZero G word M i L g.coefficients g.prior))).app s))
      (Spec.map ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset M.J // s.Nonempty})) T κ tComm κComm tκAlg (@terminalRings.{u} K
          kField kClosed kZero g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K
          kField kClosed kZero G word M i L g.coefficients g.prior) T tComm sTAlg)).app s))
      qS qT qκ (hlegS (op s)) (hlegT (op s)) (hlegκ (op s))
    exact hs.trans (congrArg (fun a => a ≫ (g.prior.cT.ι.app (op s)).left)
      (spec_three ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs
          (Category.{u} {s : Finset M.J // s.Nonempty})) g.prior.T g.pre.S (@Subalgebra.toCommRing ℤ
          K Int.instCommRing (@Field.toCommRing K kField) (@Ring.toIntAlgebra K
          (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.prior.T)
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) g.pre.S)
          (Subalgebra.inclusion g.hTpre).toAlgebra (AppendChartData.N (@NextLetter.scalarCharts.{u}
          K kField kClosed kZero G word M i L g.coefficients g.prior))).app s)
          ((@fixedScalarMap.{u,u,u} {s : Finset M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s
          : Finset M.J // s.Nonempty})) g.pre.S T (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) g.pre.S) tComm sTAlg (@stageRings.{u} K kField kClosed
          kZero g.prior.T g.pre.S G word i g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed
          kZero G word M i L g.coefficients g.prior))).app s) ((@fixedScalarMap.{u,u,u} {s : Finset
          M.J // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty})) T κ
          tComm κComm tκAlg (@terminalRings.{u} K kField kClosed kZero g.prior.T g.pre.S G word i
          g.hTpre (@NextLetter.scalarCharts.{u} K kField kClosed kZero G word M i L g.coefficients
          g.prior) T tComm sTAlg)).app s)).symm)

section Boundaries

variable {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} {i : @simpleRootIndex.{u} K kField kClosed kZero G}
    {L : NextLetter M i} {g : AppendGeometry M L}
    {T κ : Type u} [tComm : CommRing T] [κComm : CommRing κ]
    [sTAlg : Algebra g.pre.S T] [tκAlg : Algebra T κ]

/-- The carried omitted-letter models on the append prior field fibre. -/
def AppendPriorFibre.boundaries (f : AppendPriorFibre g T κ) :
    Fin word.length → Over f.cPrior.pt.left :=
  fun k => Over.mk (pullback.fst f.q (g.prior.boundaries k).hom)

/-- Projection from a fibre boundary to its carried prior boundary. -/
def AppendPriorFibre.boundaryMap (f : AppendPriorFibre g T κ) (k : Fin word.length) :
    (f.boundaries k).left ⟶ (g.prior.boundaries k).left :=
  pullback.snd f.q (g.prior.boundaries k).hom

/-- Each prior-fibre boundary is the Cartesian pullback of the carried one. -/
theorem AppendPriorFibre.boundary_cartesian (f : AppendPriorFibre g T κ)
    (k : Fin word.length) :
    IsPullback (f.boundaries k).hom (f.boundaryMap k) f.q
      (g.prior.boundaries k).hom :=
  IsPullback.of_hasPullback f.q (g.prior.boundaries k).hom

end Boundaries

end SchubertGeometry.RetainedCharacter
