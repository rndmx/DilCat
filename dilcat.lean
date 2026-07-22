import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Setoid.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Init.Data.Nat.Basic
import Init.Data.Int.Order
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
noncomputable section

open CategoryTheory
open Finset
open CategoryTheory ComposableArrows
open CategoryTheory.Localization.Construction
universe v u
namespace CategoryTheory

/-- A center in a category `C` -/
structure Center (C : Type u) [Category.{v} C] where
  I : Type u
  (nonempty : Nonempty I)
  dom : I → C
  cod : I → C
  mor : ∀ i : I, dom i ⟶ cod i
  N   : ∀ i : I, Sieve (C := C) (cod i)



variable {C : Type u} [Category.{v} C]
variable (Z : Center C)


def IsCenterMor (f : Σ X Y : C, X ⟶ Y) : Prop :=
  ∃ i : Z.I, f = ⟨Z.dom i, Z.cod i, Z.mor i⟩


/-- The MorphismProperty corresponding to IsCenterMor. -/

def CenterMorphismProperty : MorphismProperty C := fun X Y f => IsCenterMor Z ⟨X, Y, f⟩

/-- The localized category obtained by formally inverting the morphisms in CenterMorphismProperty. -/

def CenterLocalization : Type u := (CenterMorphismProperty Z).Localization

/-- The canonical functor from C to the localization. -/


def LocalizationFunctor : C ⥤ (CenterMorphismProperty Z).Localization := (CenterMorphismProperty Z).Q

def CenterSievePair : Type (max u v) :=
  Σ i : Z.I, Σ X : C, { f : X ⟶ Z.cod i // Z.N i f }

def Quv := LocQuiver (CenterMorphismProperty Z)

def inv_in_path (p : CenterSievePair Z) :
    ιPaths (CenterMorphismProperty Z) (Z.cod p.1) ⟶
    ιPaths (CenterMorphismProperty Z) (Z.dom p.1) :=
  Localization.Construction.ψ₂ (CenterMorphismProperty Z)
    (Z.mor p.1) ⟨p.1, rfl⟩

def fraction_in_path_single (p : CenterSievePair Z) :
    ιPaths (CenterMorphismProperty Z) (p.2.1) ⟶
    ιPaths (CenterMorphismProperty Z) (Z.dom p.1) :=
  Localization.Construction.ψ₁ (CenterMorphismProperty Z) p.2.2.1 ≫
    inv_in_path Z p

def fraction_in_loc_single (p : CenterSievePair Z) :
objEquiv (CenterMorphismProperty Z) (p.2.1) ⟶
objEquiv (CenterMorphismProperty Z) (Z.dom p.1) :=
 (CategoryTheory.Quotient.functor
   (relations (CenterMorphismProperty Z))).map
      (fraction_in_path_single Z p)

def IsPairMor
    (f : Σ X Y : (CenterMorphismProperty Z).Localization, X ⟶ Y) : Prop :=
  ∃ p : CenterSievePair Z,
    f =
      ⟨objEquiv (CenterMorphismProperty Z) (p.2.1),
       objEquiv (CenterMorphismProperty Z) (Z.dom p.1),
       (CategoryTheory.Quotient.functor
          (relations (CenterMorphismProperty Z))).map
             (fraction_in_path_single Z p)⟩

def FractionMorphismProperty :
       MorphismProperty (CenterMorphismProperty Z).Localization  :=
          fun X Y f => IsPairMor Z ⟨X, Y, f⟩

def IsOriginalMor
    (f : Σ X Y : (CenterMorphismProperty Z).Localization, X ⟶ Y) : Prop :=
  ∃ (X Y : C) (g : X ⟶ Y),
    f =
      ⟨objEquiv (CenterMorphismProperty Z) X,
       objEquiv (CenterMorphismProperty Z) Y,
       (CenterMorphismProperty Z).Q.map g⟩


def FractionOrOriginalMorphismProperty :
    MorphismProperty (CenterMorphismProperty Z).Localization :=
  fun {X Y} f =>
    FractionMorphismProperty Z f ∨
    IsOriginalMor Z ⟨X, Y, f⟩

def GeneratorQuiver : Quiver (CenterMorphismProperty Z).Localization where
  Hom X Y :=
    { f : X ⟶ Y // FractionOrOriginalMorphismProperty Z f }


def GeneratorObjects :=
  (CenterMorphismProperty Z).Localization

instance : Quiver (GeneratorObjects Z) :=
  GeneratorQuiver Z

def GeneratedCategory :=
  CategoryTheory.Paths (GeneratorObjects Z)

instance : Category (GeneratedCategory Z) :=
  Paths.categoryPaths _

def forgetGenerator : GeneratorObjects Z ⥤q (CenterMorphismProperty Z).Localization :=
  { obj := id,
    map := fun {X Y} f => f.1 }

def GeneratedToLocalization :
    GeneratedCategory Z ⥤ (CenterMorphismProperty Z).Localization :=
         CategoryTheory.Paths.lift (forgetGenerator Z)






noncomputable def originalFactor
    {X Y : GeneratorObjects Z}
    (g : X ⟶ Y)
    (h : IsOriginalMor Z ⟨X,Y,g.1⟩) :
    (objEquiv (CenterMorphismProperty Z)).symm X ⟶
      (objEquiv (CenterMorphismProperty Z)).symm Y :=
by
  classical
  let X₀ := Classical.choose h
  let h₁ := Classical.choose_spec h
  let Y₀ := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  have hf := Classical.choose_spec h₂
  have hX :
      X = objEquiv (CenterMorphismProperty Z) X₀ :=
    congrArg Sigma.fst hf

  have hY :
      Y = objEquiv (CenterMorphismProperty Z) Y₀ :=
    congrArg (fun s => s.2.1) hf

  rw [hX, hY]
  simp
  change X₀ ⟶ Y₀
  exact Classical.choose h₂

def DilaRel :
    HomRel (GeneratedCategory Z) :=
  fun {X Y} f g =>
    (GeneratedToLocalization Z).map f =
      (GeneratedToLocalization Z).map g

def Dila :=
  CategoryTheory.Quotient (DilaRel Z)

instance : Category (Dila Z) :=
  CategoryTheory.Quotient.category _

def DilaToLoc :
    Dila Z ⥤ (CenterMorphismProperty Z).Localization :=
  CategoryTheory.Quotient.lift
    (DilaRel Z)
    (GeneratedToLocalization Z)
    (by
      intro X Y f g h
      exact h)


instance : Congruence (DilaRel Z) where
  equivalence := by
    intro X Y
    constructor
    · intro f
      rfl
    · intro f₁ f₂ h
      exact h.symm
    · intro f₁ f₂ f₃ h₁ h₂
      dsimp [DilaRel] at h₁ h₂ ⊢
      exact h₁.trans h₂
  compLeft := by
    intro X Y Z f g g' h
    dsimp [DilaRel] at h ⊢
    rw [Functor.map_comp, Functor.map_comp, h]

  compRight := by
    intro X Y Z f f' g h
    dsimp [DilaRel] at h ⊢
    rw [Functor.map_comp, Functor.map_comp, h]



lemma DilaToLoc_faithful :
    (DilaToLoc Z).Faithful := by
  constructor
  intro X Y f g
  change CategoryTheory.Quotient.Hom (DilaRel Z) X Y at f
  unfold CategoryTheory.Quotient.Hom at f
  change CategoryTheory.Quotient.Hom (DilaRel Z) X Y at g
  unfold CategoryTheory.Quotient.Hom at g
  intro h
  revert h
  refine Quot.inductionOn f ?_
  intro p
  refine Quot.inductionOn g ?_
  intro q h
  apply Quot.sound
  dsimp [DilaRel]
  change
    (GeneratedToLocalization Z).map p =
    (GeneratedToLocalization Z).map q at h
  simpa using
    (CategoryTheory.Quotient.CompClosure.intro
      (r := DilaRel Z)
      (𝟙 X.as)
      p
      q
      (𝟙 Y.as)
      h)






def GeneratedToDila :
    GeneratedCategory Z ⥤ Dila Z :=
  CategoryTheory.Quotient.functor (DilaRel Z)

instance GeneratedToDila_full :
    (GeneratedToDila Z).Full := by
  change (CategoryTheory.Quotient.functor (DilaRel Z)).Full
  infer_instance

def CToGeneratorQuiver :
    C ⥤q GeneratorObjects Z where
  obj X := objEquiv (CenterMorphismProperty Z) X
  map {X Y} f :=
    ⟨(CenterMorphismProperty Z).Q.map f,
      Or.inr ⟨X, Y, f, rfl⟩⟩



def CatToDila :
    C ⥤ Dila Z where
  obj X :=
    Quotient.mk ((CToGeneratorQuiver Z).obj X)

  map {X Y} f :=
    (Quotient.functor (DilaRel Z)).map
      (Quiver.Hom.toPath ((CToGeneratorQuiver Z).map f))

  map_id X := by
    apply Quotient.sound
    change
      (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            ⟨(CenterMorphismProperty Z).Q.map (𝟙 X), _⟩)
        =
      𝟙 _
    simp
    simp [GeneratedToLocalization, forgetGenerator]
    rfl

  map_comp f g := by

    apply Quotient.sound
    change
      (CenterMorphismProperty Z).Q.map (f ≫ g) =
        (CenterMorphismProperty Z).Q.map f ≫
        (CenterMorphismProperty Z).Q.map g
    simp

lemma CatToDila_comp_DilaToLoc :
    CatToDila Z ⋙ DilaToLoc Z =
      LocalizationFunctor Z := by
  apply Functor.ext
  · intro X
    dsimp [LocalizationFunctor, CatToDila, DilaToLoc]
    simp
    intro Y f
    rfl
  · intro X
    change
      (GeneratedToLocalization Z).obj
          ((CToGeneratorQuiver Z).obj X) =
        (CenterMorphismProperty Z).Q.obj X
    rfl

def CatToDilaSieve
    {X : C} (N : Sieve (C := C) X) :
    Sieve (C := Dila Z) ((CatToDila Z).obj X) :=
  Sieve.functorPushforward (CatToDila Z) N

lemma fraction_comp_mor (i : Z.I) (X : C)
    (m : X ⟶ Z.cod i)
    (hm : Z.N i m) :
    (fraction_in_loc_single Z ⟨i, ⟨X, ⟨m, hm⟩⟩⟩) ≫
      (CenterMorphismProperty Z).Q.map (Z.mor i)
    =
      (CenterMorphismProperty Z).Q.map m := by
  dsimp [fraction_in_loc_single, fraction_in_path_single, inv_in_path,
    MorphismProperty.Q]

  rw [← (CategoryTheory.Quotient.functor
    (relations (CenterMorphismProperty Z))).map_comp]

  apply Quot.sound

  exact CategoryTheory.Quotient.CompClosure.intro
    (r := relations (CenterMorphismProperty Z))
    (ψ₁ (CenterMorphismProperty Z) m)
    (ψ₂ (CenterMorphismProperty Z) (Z.mor i) ⟨i, rfl⟩ ≫
      ψ₁ (CenterMorphismProperty Z) (Z.mor i))
    (𝟙 _)
    (𝟙 _)
    (Localization.Construction.relations.Winv₂
      (W := CenterMorphismProperty Z)
      (Z.mor i)
      ⟨i, rfl⟩)


def fraction_in_generated (p : CenterSievePair Z) :
    (CToGeneratorQuiver Z).obj p.2.1 ⟶
    (CToGeneratorQuiver Z).obj (Z.dom p.1) :=
  ⟨
    fraction_in_loc_single Z p,
    Or.inl ⟨p, rfl⟩
  ⟩

def fraction_in_dila_single (p : CenterSievePair Z) :
    (CatToDila Z).obj p.2.1 ⟶
    (CatToDila Z).obj (Z.dom p.1) :=
  (GeneratedToDila Z).map
    (Quiver.Hom.toPath (fraction_in_generated Z p))

theorem CatToDila_image_sieve_le_singleton (i : Z.I) :
    CatToDilaSieve Z (Z.N i) ≤
      Sieve.generate (Presieve.singleton ((CatToDila Z).map (Z.mor i))) := by

  intro X f hf
  dsimp [CatToDilaSieve, Sieve.functorPushforward] at hf

  rcases hf with ⟨Y, h, g, hg, rfl⟩

  have hfrac :
      fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
          (CatToDila Z).map (Z.mor i)
      =
      (CatToDila Z).map h := by
    apply Quotient.sound
    simp [DilaRel,
      fraction_in_dila_single,
      CatToDila,
      GeneratedToLocalization,
      forgetGenerator,
      fraction_in_path_single,
      inv_in_path]
    change
      fraction_in_loc_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
          (CenterMorphismProperty Z).Q.map (Z.mor i)
        =
      (CenterMorphismProperty Z).Q.map h

    exact fraction_comp_mor Z i Y h hg


  refine ⟨
      (CatToDila Z).obj (Z.dom i),
      g ≫ fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩,
      (CatToDila Z).map (Z.mor i),
      Presieve.singleton_self _,
      ?_
    ⟩

  calc
    (g ≫ fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩) ≫
        (CatToDila Z).map (Z.mor i)
        =
        g ≫
          (fraction_in_dila_single Z ⟨i, ⟨Y, ⟨h, hg⟩⟩⟩ ≫
            (CatToDila Z).map (Z.mor i)) := by
              rw [Category.assoc]

    _ = g ≫ (CatToDila Z).map h := by
          rw [hfrac]


lemma GeneratedCategory_morphism_induction
    (P :
      ∀ {X Y : GeneratedCategory Z},
        (f : X ⟶ Y) → Prop)
    (h_id :
      ∀ X, P (𝟙 X))
    (h_comp :
      ∀ {X Y W}
        (f : X ⟶ Y) (g : Y ⟶ W),
        P f → P g → P (f ≫ g))
        (h_gen :
  ∀ {A B : GeneratorObjects Z}
    (g : (GeneratorQuiver Z).Hom A B),
    P (Quiver.Hom.toPath g)) :
    ∀ {X Y : GeneratedCategory Z}
      (f : X ⟶ Y), P f := by

  intro X Y f
  apply CategoryTheory.Paths.induction
  · intro X
    exact h_id X
  · intro u v w p q hp
    exact h_comp p
      ((Paths.of (GeneratorObjects Z)).map q)
      hp
      (h_gen q)

variable {D : Type u} [Category.{v} D]
variable (F : C ⥤ D)



/-- Morphisms in D obtained as images of the chosen central morphisms of C. -/
def IsImageCenterMor
    (F : C ⥤ D)
    (f : Σ X Y : D, X ⟶ Y) : Prop :=
  ∃ i : Z.I,
    f =
      ⟨F.obj (Z.dom i),
       F.obj (Z.cod i),
       F.map (Z.mor i)⟩

def ImageCenterMorphismProperty :
    MorphismProperty D :=
  fun X Y f =>
    IsImageCenterMor Z F ⟨X, Y, f⟩

/-- The localization of D obtained by formally inverting
    the images of the central morphisms. -/
def ImageCenterLocalization : Type u :=
  (ImageCenterMorphismProperty Z F).Localization

instance instCategoryImageCenterLocalization :
    Category (ImageCenterLocalization Z F) := by
  dsimp [ImageCenterLocalization]
  infer_instance

/-- The canonical functor from D to the localization. -/
def ImageCenterLocalizationFunctor :
    D ⥤ ImageCenterLocalization Z F :=
  (ImageCenterMorphismProperty Z F).Q

lemma exists_factor_D
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate (Presieve.singleton (F.map (Z.mor i)))) :
    ∀ (i : Z.I) (Y : D) (n : Y ⟶ F.obj (Z.cod i)),
      (Sieve.functorPushforward F (Z.N i)).arrows n →
      ∃ q : Y ⟶ F.obj (Z.dom i),
        q ≫ F.map (Z.mor i) = n := by

  intro i Y n hn

  have hgen :
      (Sieve.generate
        (Presieve.singleton (F.map (Z.mor i)))).arrows n :=
    hsieve i n hn

  rcases hgen with ⟨X, q, g, hg, hq⟩

  rcases hg with ⟨h, rfl⟩

  exact ⟨q, hq⟩
  lemma unique_factor_D
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful) :
    ∀ (i : Z.I) (Y : D)
      (q₁ q₂ : Y ⟶ F.obj (Z.dom i)),
      q₁ ≫ F.map (Z.mor i) =
        q₂ ≫ F.map (Z.mor i) →
      q₁ = q₂ := by
  intro i Y q₁ q₂ hq

  apply hfaith.map_injective

  haveI :
      IsIso ((ImageCenterLocalizationFunctor Z F).map
        (F.map (Z.mor i))) := by
    apply CategoryTheory.MorphismProperty.Q_inverts
    exact ⟨i, rfl⟩
  apply (cancel_mono
    ((ImageCenterLocalizationFunctor Z F).map
      (F.map (Z.mor i)))).1

  simpa only [Functor.map_comp] using
    congrArg
      (fun f => (ImageCenterLocalizationFunctor Z F).map f)
      hq


lemma exists_unique_factor_D
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∀ (i : Z.I) (Y : D) (n : Y ⟶ F.obj (Z.cod i)),
      (Sieve.functorPushforward F (Z.N i)).arrows n →
      ∃! q : Y ⟶ F.obj (Z.dom i),
        q ≫ F.map (Z.mor i) = n := by
  intro i Y n hn

  obtain ⟨q, hq⟩ := exists_factor_D Z F hsieve i Y n hn

  refine ⟨q, hq, ?_⟩

  intro q' hq'

  exact unique_factor_D Z F hfaith i Y q' q (by
    rw [hq', hq])

def uniqueFactor_D
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i))))
    (i : Z.I) (Y : C)
    (n : Y ⟶ Z.cod i)
    (hn : Z.N i n) :
    F.obj Y ⟶ F.obj (Z.dom i) := by

  have hn' :
      (Sieve.functorPushforward F (Z.N i)).arrows (F.map n) := by
    refine ⟨Y, n, 𝟙 _, hn, ?_⟩
    simp

  exact Classical.choose
    (exists_unique_factor_D Z F hfaith hsieve
      i (F.obj Y) (F.map n) hn')

def mapGenerator
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i))))
    {X Y : GeneratorObjects Z}
    (g : (GeneratorQuiver Z).Hom X Y) :
    F.obj ((objEquiv (CenterMorphismProperty Z)).symm X) ⟶
    F.obj ((objEquiv (CenterMorphismProperty Z)).symm Y) := by

  classical

  by_cases h : FractionMorphismProperty Z g.1

  · let p := Classical.choose h
    let hp := Classical.choose_spec h

    have hX :
    X = objEquiv (CenterMorphismProperty Z) p.snd.fst := by
        dsimp [p] at hp
        exact congrArg Sigma.fst hp

    have hY :
    Y = objEquiv (CenterMorphismProperty Z) (Z.dom p.fst) := by
        dsimp [p] at hp
        exact congrArg (fun s => s.2.1) hp

    rw [hX, hY]

    exact
      uniqueFactor_D Z F hfaith hsieve
        p.1 p.2.1 p.2.2.1 p.2.2.2

  · have horig : IsOriginalMor Z ⟨X, ⟨Y, g.1⟩⟩ :=
      g.property.resolve_left h

    exact F.map (originalFactor Z g horig)

def localizationMap :
    (CenterMorphismProperty Z).Localization ⥤
      ImageCenterLocalization Z F := by

  apply Localization.Construction.lift
    (W := CenterMorphismProperty Z)
    (F ⋙ ImageCenterLocalizationFunctor Z F)

  intro X Y f hf

  rcases hf with ⟨i, hi⟩

  have hX : X = Z.dom i := by
    exact congrArg Sigma.fst hi

  have hY : Y = Z.cod i := by
    exact congrArg (fun s => s.2.1) hi

  subst X
  subst Y


  apply CategoryTheory.MorphismProperty.Q_inverts
  refine ⟨i, ?_⟩
  simp
  cases hi
  rfl





theorem localizationMap_comp_Q :
    (CenterMorphismProperty Z).Q ⋙ localizationMap Z F =
      F ⋙ ImageCenterLocalizationFunctor Z F := by
  sorry


def Gq
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    GeneratorObjects Z ⥤q D :=
{
  obj := fun X =>
    F.obj ((objEquiv (CenterMorphismProperty Z)).symm X)

  map := by
    intro X Y g
    exact mapGenerator Z F hfaith hsieve g
}

def H
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    GeneratedCategory Z ⥤ D :=
  Paths.lift (Gq Z F hfaith hsieve)



lemma H_map_original
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate (Presieve.singleton (F.map (Z.mor i))))
    {X Y : C} (f : X ⟶ Y) :
    (H Z F hfaith hsieve).map
      ((CToGeneratorQuiver Z).map f).toPath =
      F.map f := by
  sorry



lemma  generatedLocalization_commutes
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F =
      GeneratedToLocalization Z ⋙ localizationMap Z F := by
  sorry





theorem exists_Dila_factor
    (hfaith :
      (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∃ (G : Dila Z ⥤ D),
      CatToDila Z ⋙ G = F := by



      have hrel :
      ∀ {X Y : GeneratedCategory Z}
        (f g : X ⟶ Y),
        DilaRel Z f g →
        (H Z F hfaith hsieve).map f =
        (H Z F hfaith hsieve).map g := by
        intro X Y f g hfg

        apply (ImageCenterLocalizationFunctor Z F).map_injective

        have hcomm :=
          generatedLocalization_commutes Z F hfaith hsieve

        change
          (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).map f =
          (H Z F hfaith hsieve ⋙ ImageCenterLocalizationFunctor Z F).map g



        rw [hcomm]

        simpa only [Functor.comp_map] using
          congrArg
            (fun k => (localizationMap Z F).map k)
            hfg

      let G : Dila Z ⥤ D :=
          CategoryTheory.Quotient.lift
            (DilaRel Z)
            (H Z F hfaith hsieve)
            (by
              intro X Y f g hfg
              exact hrel f g hfg)



      refine ⟨G, ?_⟩


      apply Functor.ext

      · intro X Y f

        simp only [Functor.comp_map]

        simp [CatToDila, G]

        change
          (H Z F hfaith hsieve).map
              ((CToGeneratorQuiver Z).map f).toPath =
            F.map f

        exact H_map_original Z F hfaith hsieve f


      · intro X
        simp [CatToDila, G, H, Gq]
        rfl




lemma Dila_factor_unique_on_C
    (G₁ G₂ : Dila Z ⥤ D)
    (h₁ : CatToDila Z ⋙ G₁ = F)
    (h₂ : CatToDila Z ⋙ G₂ = F) :
    CatToDila Z ⋙ G₁ = CatToDila Z ⋙ G₂ := by
  exact h₁.trans h₂.symm

lemma map_eq_of_agree_on_C
    {X Y : C}
    (G₁ G₂ : Dila Z ⥤ D)
    (h₁ : CatToDila Z ⋙ G₁ = F)
    (h₂ : CatToDila Z ⋙ G₂ = F)
    (f : X ⟶ Y) :
    G₁.map ((CatToDila Z).map f) =
      eqToHom
        (congrArg (fun H => H.obj X)
          (h₁.trans h₂.symm)) ≫
        G₂.map ((CatToDila Z).map f) ≫
      eqToHom
        (congrArg (fun H => H.obj Y)
          (h₁.trans h₂.symm)).symm := by

  apply Functor.congr_hom (h₁.trans h₂.symm)


lemma Dila_factor_unique_fraction
    (G₁ G₂ : Dila Z ⥤ D)
    (hfaith :
    (ImageCenterLocalizationFunctor Z F).Faithful)
    (h₁ : CatToDila Z ⋙ G₁ = F)
    (h₂ : CatToDila Z ⋙ G₂ = F) :
    ∀ (i : Z.I) (X : C)
      (n : X ⟶ Z.cod i)
      (hn : Z.N i n),
      G₁.map
        (fraction_in_dila_single Z
          ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
      =
      eqToHom (by
        have := congrArg (fun H => H.obj X)
          (Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂)
        exact this)
      ≫
      G₂.map
        (fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
      ≫
      eqToHom (by
        have := congrArg (fun H => H.obj (Z.dom i))
          (Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂)
        exact this.symm) :=  by
  intro i X n hn

  let b :=
    fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩

  have hb :
      b ≫ (CatToDila Z).map (Z.mor i) =
        (CatToDila Z).map n := by
    apply Quotient.sound
    change
      (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            (fraction_in_generated Z
              ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)) ≫
        (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            ((CToGeneratorQuiver Z).map (Z.mor i)))
      =
      (GeneratedToLocalization Z).map
          (Quiver.Hom.toPath
            ((CToGeneratorQuiver Z).map n))

    rw [← Functor.map_comp]

    change
      fraction_in_loc_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩ ≫
          (CenterMorphismProperty Z).Q.map (Z.mor i)
        =
      (CenterMorphismProperty Z).Q.map n

    exact fraction_comp_mor Z i X n hn

  have h₁b :
      G₁.map b ≫
          G₁.map ((CatToDila Z).map (Z.mor i))
        =
      G₁.map ((CatToDila Z).map n) := by
    rw [← Functor.map_comp]
    rw [hb]

  have h₂b :
      G₂.map b ≫
          G₂.map ((CatToDila Z).map (Z.mor i))
        =
      G₂.map ((CatToDila Z).map n) := by
    rw [← Functor.map_comp]
    rw [hb]

  have hmono :
      Mono (F.map (Z.mor i)) := by
    constructor
    intro W u v huv

    apply hfaith.map_injective

    haveI :
        IsIso ((ImageCenterLocalizationFunctor Z F).map
          (F.map (Z.mor i))) := by
      apply CategoryTheory.MorphismProperty.Q_inverts
        (ImageCenterMorphismProperty Z F)
      exact ⟨i, rfl⟩

    apply (cancel_mono
      ((ImageCenterLocalizationFunctor Z F).map
        (F.map (Z.mor i)))).1

    simpa only [Functor.map_comp] using
      congrArg
        (fun f =>
          (ImageCenterLocalizationFunctor Z F).map f)
        huv


  have hcancel :
      ∀ {u v :
        G₁.obj ((CatToDila Z).obj X) ⟶
          G₁.obj ((CatToDila Z).obj (Z.dom i))},
      u ≫ G₁.map ((CatToDila Z).map (Z.mor i)) =
        v ≫ G₁.map ((CatToDila Z).map (Z.mor i)) →
      u = v := by

    intro u v huv

    haveI :
        Mono ((CatToDila Z ⋙ G₁).map (Z.mor i)) := by
      rw [h₁]
      exact hmono

    haveI :
        Mono (G₁.map ((CatToDila Z).map (Z.mor i))) := by
      change Mono ((CatToDila Z ⋙ G₁).map (Z.mor i))
      infer_instance

    exact
      (cancel_mono
        (G₁.map ((CatToDila Z).map (Z.mor i)))).1 huv

  apply hcancel


  rw [h₁b]

  have hn_map :
      G₁.map ((CatToDila Z).map n) =
        eqToHom
          (congrArg (fun H => H.obj X)
            (h₁.trans h₂.symm)) ≫
        G₂.map ((CatToDila Z).map n) ≫
        eqToHom
          (congrArg (fun H => H.obj (Z.cod i))
            (h₁.trans h₂.symm)).symm :=
    map_eq_of_agree_on_C (Z := Z) (F := F)
      G₁ G₂ h₁ h₂ n

  rw [hn_map]

  rw [← h₂b]

  have hdi :
    G₁.map ((CatToDila Z).map (Z.mor i)) =
      eqToHom
        (congrArg (fun H => H.obj (Z.dom i))
          (h₁.trans h₂.symm)) ≫
      G₂.map ((CatToDila Z).map (Z.mor i)) ≫
      eqToHom
        (congrArg (fun H => H.obj (Z.cod i))
          (h₁.trans h₂.symm)).symm :=
  map_eq_of_agree_on_C (Z := Z) (F := F)
    G₁ G₂ h₁ h₂ (Z.mor i)

  rw [hdi]
  simp only [Category.assoc]
  subst b
  simp


lemma Subtype.ext_val
    {α : Type*} {p : α → Prop} {a b : Subtype p}
    (h : a.val = b.val) : a = b :=
by
  exact Subtype.ext h

lemma Subtype.val_eq_of_eq
    {α : Type*} {p : α → Prop} {a b : Subtype p}
    (h : a = b) : a.val = b.val :=
by
  simpa using congrArg Subtype.val h


lemma GeneratorQuiver.ext_val
    {A B : (CenterMorphismProperty Z).Localization}
    {f g : @Quiver.Hom _ (GeneratorQuiver Z) A B}
    (h : f.val = g.val) : f = g := by
  exact Subtype.ext h



lemma Generated_factor_unique_map
    (G₁ G₂ :
      Dila Z ⥤ D)
    (h_obj :
      ∀ X : Dila Z, G₁.obj X = G₂.obj X)
    (h_mor :
      ∀ {X Y : C} (f : X ⟶ Y),
        G₁.map ((CatToDila Z).map f) =
          eqToHom (h_obj ((CatToDila Z).obj X)) ≫
          G₂.map ((CatToDila Z).map f) ≫
          eqToHom (h_obj ((CatToDila Z).obj Y)).symm)
    (h_fraction :
      ∀ (i : Z.I) (X : C)
        (n : X ⟶ Z.cod i)
        (hn : Z.N i n),
        G₁.map
          (fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩)
        =
        eqToHom (h_obj ((CatToDila Z).obj X)) ≫
          G₂.map
            (fraction_in_dila_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) ≫
          eqToHom (h_obj ((CatToDila Z).obj (Z.dom i))).symm)
    {X Y : Dila Z}
    (f : X ⟶ Y) :
    G₁.map f =
      eqToHom (h_obj X) ≫
        G₂.map f ≫
        eqToHom (h_obj Y).symm := by








  letI : (GeneratedToDila Z).Full := GeneratedToDila_full Z



  obtain ⟨g, hg⟩ := (GeneratedToDila Z).map_surjective f

  rw [← hg]

  let P :=
    fun {A B : GeneratedCategory Z} (k : A ⟶ B) =>
      G₁.map ((GeneratedToDila Z).map k) =
        eqToHom (h_obj ((GeneratedToDila Z).obj A)) ≫
          G₂.map ((GeneratedToDila Z).map k) ≫
          eqToHom (h_obj ((GeneratedToDila Z).obj B)).symm

  have hgP : P g := by
    apply GeneratedCategory_morphism_induction Z P

    · intro A
      simp [P]

    · intro A B C f g hf hg
      dsimp [P] at *
      rw [Functor.map_comp]
      rw [Functor.map_comp]
      rw [hf, hg]
      simp [Category.assoc]


    · intro A B g
      rcases g.2 with h | h

      ·
        rcases h with ⟨p, hp⟩
        rcases p with ⟨i, X, n, hn⟩

        have hA :
            A = objEquiv (CenterMorphismProperty Z) X := by
          exact congrArg Sigma.fst hp

        have hB :
            B = objEquiv (CenterMorphismProperty Z) (Z.dom i) := by
          exact congrArg (fun s => s.2.1) hp

        subst A
        subst B

        dsimp [P]



        have hg :
            g =
              ⟨
                (Quotient.functor (relations (CenterMorphismProperty Z))).map
                  (fraction_in_path_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩),
                Or.inl ⟨⟨i, ⟨X, ⟨n, hn⟩⟩⟩, rfl⟩
              ⟩ := by
          apply GeneratorQuiver.ext_val Z
          have hval :
              g.val =
                (Quotient.functor (relations (CenterMorphismProperty Z))).map
                  (fraction_in_path_single Z ⟨i, ⟨X, ⟨n, hn⟩⟩⟩) := by

                  simpa [Prod.ext_iff] using hp



          exact hval






        rw [hg]
        exact h_fraction i X n hn

      · rcases h with ⟨X, Y, g₁, hp⟩

        have hA :
            A = objEquiv (CenterMorphismProperty Z) X := by
          exact congrArg Sigma.fst hp

        have hB :
            B = objEquiv (CenterMorphismProperty Z) Y := by
          exact congrArg (fun s => s.2.1) hp

        subst A
        subst B

        dsimp [P]

        have hg :
            g =
              ⟨
                (CenterMorphismProperty Z).Q.map g₁,
                Or.inr ⟨X, Y, g₁, rfl⟩
              ⟩ := by

               apply GeneratorQuiver.ext_val Z
               simpa [Prod.ext_iff] using hp

        rw [hg]

        exact h_mor g₁





  exact hgP






lemma localization_obj_eq_Q_obj
    (X : (CenterMorphismProperty Z).Localization) :
    ∃ Y : C, (CenterMorphismProperty Z).Q.obj Y = X := by
  let e := (CategoryTheory.Localization.Construction.objEquiv
      (CenterMorphismProperty Z))
  refine ⟨e.invFun X, ?_⟩
  exact e.apply_symm_apply X

lemma Dila_obj_eq_C_obj :
    ∀ (X : Dila Z), ∃ Y : C, (CatToDila Z).obj Y = X := by
  intro X
  obtain ⟨Y, hY⟩ :=
    localization_obj_eq_Q_obj Z X.1
  refine ⟨Y, ?_⟩
  cases X
  dsimp [CatToDila]
  cases hY
  rfl

theorem Dila_factor_unique
    (G₁ G₂ :
        Dila Z ⥤ D)
    (h₁ :
      CatToDila Z ⋙ G₁ =
        F)
    (h₂ :
      CatToDila Z ⋙ G₂ =
        F)
    (hfaith :
       (ImageCenterLocalizationFunctor Z F).Faithful)
     :
    G₁ = G₂ := by
  have h_obj :
      ∀ X : Dila Z, G₁.obj X = G₂.obj X := by
      intro X
      obtain ⟨Y, hY⟩ := Dila_obj_eq_C_obj Z X
      rw [← hY]
      have h1Y := congrArg (fun H : C ⥤ D => H.obj Y) h₁
      have h2Y := congrArg (fun H : C ⥤ D => H.obj Y) h₂
      exact h1Y.trans h2Y.symm

  apply CategoryTheory.Functor.ext
  · intro X Y f
    exact Generated_factor_unique_map
      Z G₁ G₂
     (by

        assumption)
     (   by
                intro X Y f

                have H :
                    CatToDila Z ⋙ G₁ = CatToDila Z ⋙ G₂ :=
                  Dila_factor_unique_on_C Z F G₁ G₂ h₁ h₂

                have hm :
                    G₁.map ((CatToDila Z).map f) ≍
                    G₂.map ((CatToDila Z).map f) := by
                  have hm' :
                      (CatToDila Z ⋙ G₁).map f ≍
                      (CatToDila Z ⋙ G₂).map f := by
                    rw [H]
                  exact hm'

                exact (conj_eqToHom_iff_heq
                          (G₁.map ((CatToDila Z).map f))
                          (G₂.map ((CatToDila Z).map f))
                          (h_obj ((CatToDila Z).obj X))
                          (h_obj ((CatToDila Z).obj Y))).2 hm )
       (by
        intro i X n hn
        exact Dila_factor_unique_fraction
          Z F G₁ G₂ (by assumption) h₁ h₂ i X n hn)
        f




theorem Dila_universal_property
    (F : C ⥤ D)
    (hfaith :
       (ImageCenterLocalizationFunctor Z F).Faithful)
    (hsieve :
      ∀ (i : Z.I),
        Sieve.functorPushforward F (Z.N i) ≤
          Sieve.generate
            (Presieve.singleton (F.map (Z.mor i)))) :
    ∃! (G : Dila Z ⥤ D),
      CatToDila Z ⋙ G =
        F := by

  obtain ⟨G, hG⟩ :=
    exists_Dila_factor Z F hfaith hsieve

  refine ⟨G, hG, ?_⟩

  intro G' hG'

  exact Dila_factor_unique
    Z
    F
    G'
    G
    hG'
    hG
    hfaith







end CategoryTheory
