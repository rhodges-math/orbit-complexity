import OrbitComplexity.SchubertGeometry.Deodhar.PrefixMaps


/-! # Cartesian charts on word cells

A regular frame identifies an additive extension with a pullback of the next-cell projection.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups SchubertGeometry
open GroupActions GroupActions.Variety CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private theorem assoc_points {K : Type u} [Field K] {Q Z : Variety K}
    {A B C D : Over (Spec (CommRingCat.of K))} (a : Q.toOver ⟶ A)
    (b : A ⟶ B) (c : B ⟶ C) (d : C ⟶ D) (j : D ⟶ Z.toOver) (q : Q.points) :
    mapPoints (a ≫ (b ≫ c ≫ d) ≫ j) q = mapPoints (a ≫ b ≫ c ≫ d ≫ j) q := by
  apply congrArg (fun f : Q.toOver ⟶ Z.toOver => mapPoints f q)
  simp only [Category.assoc]

attribute [local irreducible] wordCellExtensionIso wordCellStep
  rankOneLiftIso rankOneCellProjection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)
  (n : ℕ) (hn : n < word.length)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
    (simpleWeylWord G.rootBase (word.take n)) word[n]))
  (X : Variety K)
  (f : X.toOver ⟶ (schubertCell G (simpleWeylWord G.rootBase (word.take n))).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫
    schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)))

/-- The prefix point formula holds with its extension map grouped as one composite. -/
private theorem wordLiftMap_grouped (Q : Variety K)
    (a : Q.toOver ⟶ X.toOver ⊗ (additiveVariety K).toOver) (q : Q.points) :
    type_of% ((assoc_points a
      (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n]
        hi X f g hg).hom
      (pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi))
      (wordCellExtensionIso G word n hn).hom
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) q).trans
        (wordLiftMap_points G word n hn hi X f g hg Q a q)) :=
  (assoc_points a
      (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n]
        hi X f g hg).hom
      (pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi))
      (wordCellExtensionIso G word n hn).hom
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) q).trans
        (wordLiftMap_points G word n hn hi X f g hg Q a q)

end
end SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups SchubertGeometry
open GroupActions GroupActions.Variety CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

/-- A three-factor composite with its intermediate objects fixed. -/
@[irreducible] private def compositeThree {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : A ⟶ E := f ≫ g ≫ h

private theorem compositeThree_eq {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : compositeThree f g h = f ≫ g ≫ h := by
  unfold compositeThree
  rfl

private theorem replace_points {K : Type u} [Field K] {Q Z : Variety K}
    {A B : Over (Spec (CommRingCat.of K))} (m n : A ⟶ B) (h : m = n)
    (a : Q.toOver ⟶ A) (j : B ⟶ Z.toOver) (q : Q.points) {v : Z.points}
    (hn : mapPoints (a ≫ n ≫ j) q = v) : mapPoints (a ≫ m ≫ j) q = v :=
  (congrArg (fun f : A ⟶ B => mapPoints (a ≫ f ≫ j) q) h).trans hn

attribute [local irreducible] wordCellExtensionIso wordCellStep
  rankOneLiftIso rankOneCellProjection
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)
  (n : ℕ) (hn : n < word.length)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
    (simpleWeylWord G.rootBase (word.take n)) word[n]))
  (X : Variety K)
  (f : X.toOver ⟶ (schubertCell G (simpleWeylWord G.rootBase (word.take n))).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫
    schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)))

/-- The extension acts by its regular frame with the map grouped as one composite. -/
private theorem wordComposite_points (Q : Variety K)
    (a : Q.toOver ⟶ X.toOver ⊗ (additiveVariety K).toOver) (q : Q.points) :
    type_of% (replace_points (K := K) (Q := Q) (Z := flagVariety G)
      (compositeThree
        (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X f g hg).hom
        (pullback.snd f (rankOneCellProjection G
          (simpleWeylWord G.rootBase (word.take n)) word[n] hi))
        (wordCellExtensionIso G word n hn).hom) _
      (compositeThree_eq _ _ _) a
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) q
      (wordLiftMap_grouped G word n hn hi X f g hg Q a q)) :=
  replace_points (K := K) (Q := Q) (Z := flagVariety G)
    (compositeThree
      (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n)) word[n] hi X f g hg).hom
      (pullback.snd f (rankOneCellProjection G
        (simpleWeylWord G.rootBase (word.take n)) word[n] hi))
      (wordCellExtensionIso G word n hn).hom) _
    (compositeThree_eq _ _ _) a
    (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) q
    (wordLiftMap_grouped G word n hn hi X f g hg Q a q)

end
end SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section

private theorem chart_isPullback {C : Type*} [Category C] [HasPullbacks C]
    {A X Y D B : C} (f : X ⟶ B) (p : Y ⟶ B)
    (e : A ≅ pullback f p) (j : Y ≅ D) (q : D ⟶ B) (a : A ⟶ X)
    (he : e.hom ≫ pullback.fst f p = a) (hj : j.hom ≫ q = p) :
    IsPullback a (e.hom ≫ pullback.snd f p ≫ j.hom) f q := by
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p ≫ j.hom) f q :=
    (IsPullback.of_hasPullback f p).of_iso (.refl _) (.refl _) j (.refl _)
      (by simp) (by simp) (by simp)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hj.symm)
  exact hpb.of_iso' e (.refl _) (.refl _) (.refl _)
    (by simpa using he) (by simp) (by simp) (by simp)

private theorem replace_snd {C : Type*} [Category C] {A X D B : C}
    (a : A ⟶ X) (f : X ⟶ B) (q : D ⟶ B) (m n : A ⟶ D) (hm : m = n)
    (hn : IsPullback a n f q) : IsPullback a m f q :=
  Eq.mpr (congrArg (fun k => IsPullback a k f q) hm) hn

private theorem compositeThree_value {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : compositeThree f g h = f ≫ g ≫ h := by
  unfold compositeThree
  rfl

/-- A chart gives a cartesian map with each property proved for its composite. -/
private theorem chart_exists {C : Type*} [Category C] [HasPullbacks C]
    {A X Y D B : C} (f : X ⟶ B) (p : Y ⟶ B)
    (e : A ≅ pullback f p) (j : Y ≅ D) (q : D ⟶ B) (a : A ⟶ X)
    (he : e.hom ≫ pullback.fst f p = a) (hj : j.hom ≫ q = p)
    (P : (A ⟶ D) → Prop)
    (hP : P (compositeThree e.hom (pullback.snd f p) j.hom)) :
    ∃ m : A ⟶ D, P m ∧ IsPullback a m f q := by
  refine ⟨compositeThree e.hom (pullback.snd f p) j.hom, hP, ?_⟩
  exact replace_snd a f q _ _ (compositeThree_value _ _ _)
    (chart_isPullback f p e j q a he hj)

end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits
namespace SchubertGeometry.Deodhar
noncomputable section

/-- A chart map is preserved as a morphism when transporting its cartesian square. -/
private theorem chart_from_hom {C : Type*} [Category C] [HasPullbacks C]
    {A X Y D B : C} (f : X ⟶ B) (p : Y ⟶ B)
    (e : A ≅ pullback f p) (jh : Y ⟶ D) [IsIso jh] (q : D ⟶ B) (a : A ⟶ X)
    (he : e.hom ≫ pullback.fst f p = a) (hj : jh ≫ q = p)
    (P : (A ⟶ D) → Prop)
    (hP : P (compositeThree e.hom (pullback.snd f p) jh)) :
    ∃ m : A ⟶ D, P m ∧ IsPullback a m f q :=
  chart_exists f p e (asIso jh) q a he hj P hP

end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups SchubertGeometry
open GroupActions GroupActions.Variety CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
attribute [local irreducible] wordCellExtensionIso wordCellStep
  rankOneLiftIso rankOneCellProjection
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)
  (n : ℕ) (hn : n < word.length)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
    (simpleWeylWord G.rootBase (word.take n)) (word[n]'hn)))
  (X : Variety K)
  (f : X.toOver ⟶ (schubertCell G (simpleWeylWord G.rootBase (word.take n))).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫
    schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)))


/-- The Cartesian chart point formula uses the specified source and flag varieties. -/
private theorem wordPointsTyped (Q : Variety K)
    (a : Q.toOver ⟶ X.toOver ⊗ (additiveVariety K).toOver) (q : Q.points) :
    mapPoints (X := Q) (Y := flagVariety G)
      (a ≫ compositeThree
        (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n))
          (word[n]'hn) hi X f g hg).hom
        (pullback.snd f (rankOneCellProjection G
          (simpleWeylWord G.rootBase (word.take n)) (word[n]'hn) hi))
        (wordCellExtensionIso G word n hn).hom ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1)))) q =
      mapPoints (X := Q) (Y := reductiveVariety G)
        (a ≫ fst X.toOver (additiveVariety K).toOver ≫ g) q •
      mapPoints (X := Q) (Y := flagVariety G)
        (a ≫ snd X.toOver (additiveVariety K).toOver ≫
          (simpleCellIso G (word[n]'hn)).hom ≫
          schubertCellInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem (word[n]'hn))) q := by
  exact wordComposite_points G word n hn hi X f g hg Q a q

end
end SchubertGeometry.Deodhar

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry.Deodhar
noncomputable section
universe u
attribute [local irreducible] wordCellExtensionIso wordCellStep
  rankOneLiftIso rankOneCellProjection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (word : List G.rootBase.support)
  (n : ℕ) (hn : n < word.length)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm
    (simpleWeylWord G.rootBase (word.take n)) (word[n]'hn)))
  (X : Variety K)
  (f : X.toOver ⟶ (schubertCell G (simpleWeylWord G.rootBase (word.take n))).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫
    schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)))


include hi hg in
/-- A regular frame gives a coordinate map cartesian over the preceding cell. -/
theorem wordChartExists
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    ∃ m : X.toOver ⊗ (additiveVariety K).toOver ⟶ (wordCell G word (n + 1)).toOver,
      (∀ (Q : Variety K) (a : Q.toOver ⟶ X.toOver ⊗ (additiveVariety K).toOver)
        (q : Q.points),
        mapPoints (X := Q) (Y := flagVariety G)
          (a ≫ m ≫ schubertCellInclusion G
            (simpleWeylWord G.rootBase (word.take (n + 1)))) q =
          mapPoints (X := Q) (Y := reductiveVariety G)
            (a ≫ fst X.toOver (additiveVariety K).toOver ≫ g) q •
          mapPoints (X := Q) (Y := flagVariety G)
            (a ≫ snd X.toOver (additiveVariety K).toOver ≫
              (simpleCellIso G (word[n]'hn)).hom ≫ schubertCellInclusion G
                (RootPairing.weylGroup.ofIdx G.rootSystem (word[n]'hn))) q) ∧
      IsPullback
        (P := X.toOver ⊗ (additiveVariety K).toOver) (X := X.toOver)
        (Y := (wordCell G word (n + 1)).toOver) (Z := (schubertCell G (simpleWeylWord G.rootBase
          (word.take n))).toOver)
        (fst X.toOver (additiveVariety K).toOver) m f
        (wordCellStep G word hred n) := by
  have hc := chart_from_hom
    (C := Over (Spec (CommRingCat.of K)))
    (A := X.toOver ⊗
      (additiveVariety K).toOver)
    (X := X.toOver)
    (D := (wordCell G word (n + 1)).toOver)
    f
    (rankOneCellProjection G (simpleWeylWord G.rootBase (word.take n))
      (word[n]'hn) hi)
    (rankOneLiftIso G (simpleWeylWord G.rootBase (word.take n))
      (word[n]'hn) hi
      X f
      g
      hg)
    (wordCellExtensionIso G word n hn).hom (wordCellStep G word hred n)
    (fst X.toOver (additiveVariety K).toOver)
    (rankOneLiftIso_fst G (simpleWeylWord G.rootBase (word.take n))
      (word[n]'hn) hi
      X f
      g
      hg)
    (wordCellExtensionIso_projection G word hred n hn
      hi)
    (fun m => ∀ (Q : Variety K)
      (a : Q.toOver ⟶ X.toOver ⊗
        (additiveVariety K).toOver) (q : Q.points),
      mapPoints (X := Q) (Y := flagVariety G)
        (a ≫ m ≫ schubertCellInclusion G
          (simpleWeylWord G.rootBase (word.take (n + 1)))) q =
        mapPoints (X := Q) (Y := reductiveVariety G)
          (a ≫ fst X.toOver
            (additiveVariety K).toOver ≫ g) q •
        mapPoints (X := Q) (Y := flagVariety G)
          (a ≫ snd X.toOver
            (additiveVariety K).toOver ≫ (simpleCellIso G (word[n]'hn)).hom ≫
              schubertCellInclusion G
                (RootPairing.weylGroup.ofIdx G.rootSystem (word[n]'hn))) q)
    (fun Q a q => wordPointsTyped G word n hn
      hi
      X f
      g
      hg Q a q)
  exact hc

end
end SchubertGeometry.Deodhar
