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
noncomputable section

open CategoryTheory
open Finset
open CategoryTheory ComposableArrows
open CategoryTheory.Localization.Construction
universe v u

/-- A center in a category `C` -/
structure Center (C : Type u) [Category.{v} C] where
  I : Type u
  (nonempty : Nonempty I)
  dom : I → C
  cod : I → C
  mor : ∀ i : I, dom i ⟶ cod i
  N   : ∀ i : I, Sieve (C := C) (cod i)

namespace Dilatation

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




structure Fraction :=
  (k : ℕ)
  (Xs : ℕ → C) /-  restrict that to integers smaller or eq to  to k+1-/
  (Ys : ℕ → C) /-  restrict that to integers smaller or eq to  to k-/
  (i  : ℕ → Z.I)  /- add here that i < k -/
  (n_orig : Π (j : {j // j < k}), Xs j ⟶ Ys j)
  (n_dom : ∀ j : {j // j < k}, Z.dom (i j) = Xs (j+1))
  (n_cod : ∀ j : {j // j < k}, Z.cod (i j) = Ys j)
  n : Π (j : {j // j < k}), Xs j ⟶ Z.cod (i j) :=
   λ j => n_orig j ≫ eqToHom (n_cod j).symm
  (n_in_N : ∀ j : {j // j < k }, Z.N (i j) (n j))
  (a : Xs (k) ⟶ Xs (k+1))
  (a_dom : Z.dom (i (k)) = Xs (k))


def Quiv := LocQuiver (CenterMorphismProperty Z)

-- Define inv_in_path
def inv_in_path (F: Fraction Z)  (j : {j // j < (F.k )}):
  ιPaths (CenterMorphismProperty Z) (Z.cod (F.i j)) ⟶
  ιPaths (CenterMorphismProperty Z) (Z.dom (F.i j)) :=
  Localization.Construction.ψ₂ (CenterMorphismProperty Z)
  (Z.mor (F.i j)) ⟨F.i ↑j, rfl⟩


def fraction_in_path_single (F : Fraction Z) (j : {j // j < F.k }) :
  ιPaths (CenterMorphismProperty Z) (F.Xs j) ⟶
  ιPaths (CenterMorphismProperty Z) (F.Xs (j+1)) :=
  Localization.Construction.ψ₁ (CenterMorphismProperty Z) (F.n j) ≫
    inv_in_path Z F j ≫
      eqToHom (congrArg (ιPaths (CenterMorphismProperty Z)) (F.n_dom j))


#check  Setoid (LocQuiver (CenterMorphismProperty Z))
#check   (relations (CenterMorphismProperty Z))


def fraction_in_path_seq (F : Fraction Z) :
  Π (n : {n // n < F.k }),
    ιPaths (CenterMorphismProperty Z) (F.Xs 0) ⟶ ιPaths (CenterMorphismProperty Z) (F.Xs (n+1))
| ⟨0, h⟩ => fraction_in_path_single Z F ⟨0, h⟩
| ⟨n+1, h⟩ =>
  let prev : {j // j < F.k } := ⟨n, Nat.lt_of_succ_lt h⟩
  fraction_in_path_seq F prev ≫ fraction_in_path_single Z F ⟨n+1, h⟩


def fraction_in_path_last (F : Fraction Z) :
    ιPaths (CenterMorphismProperty Z) (F.Xs 0) ⟶ ιPaths (CenterMorphismProperty Z) (F.Xs (F.k)):=
if h : F.k = 0 then
  eqToHom (congrArg (ιPaths (CenterMorphismProperty Z)) (by rw [h]))  -- case k = 0
else
  let x := F.k - 1
  have hx : F.k-1 < F.k := Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.succ_pos _)
  fraction_in_path_seq Z F ⟨F.k - 1, hx⟩ ≫
  eqToHom (congrArg (ιPaths (CenterMorphismProperty Z)) (congrArg (F.Xs) (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h))))



def fraction_in_path_full (F : Fraction Z) :
    ιPaths (CenterMorphismProperty Z) (F.Xs 0) ⟶ ιPaths (CenterMorphismProperty Z) (F.Xs (F.k+1)):=
    fraction_in_path_last Z F  ≫
      Localization.Construction.ψ₁ (CenterMorphismProperty Z) (F.a)


/-def fraction_in_loc_single (F : Fraction Z) (j : {j // j < F.k + 1}) :
objEquiv (CenterMorphismProperty Z) (F.Xs j) ⟶
objEquiv (CenterMorphismProperty Z) (F.Xs (j+1)) :=
 (CategoryTheory.Quotient.functor (relations (CenterMorphismProperty Z))).map (fraction_in_path_single Z F j) -/


def fraction_in_loc_full (F : Fraction Z)  :
objEquiv (CenterMorphismProperty Z) (F.Xs 0) ⟶
objEquiv (CenterMorphismProperty Z) (F.Xs (F.k+1)) :=
 (CategoryTheory.Quotient.functor (relations (CenterMorphismProperty Z))).map (fraction_in_path_full Z F)



/- The composition of X0--->Y0--->X1...--->X_n--->Y_n--->Xn+1--a->Xn+2 with
X0'--n0'->Y0'--->X1'...--->X_n'--->Y_n'--->X'n'+1--a'->X'n'+2  is the concatenation
   except that we compose n0' and a -/
def composition (F F' : Fraction Z) (compat : F.Xs (F.k + 1) = F'.Xs 0) : Fraction Z :=
{ k := F.k + F'.k ,  -- example: total length
  Xs := fun n =>
    if h : n ≤ F.k  then
      F.Xs n
    else
      F'.Xs (n - (F.k )),  -- shift F'’s indices
  Ys := fun n =>
    if h : n < F.k  then
      F.Ys n
    else
      F'.Ys (n - (F.k )),
  i := fun n =>
    if h : n < F.k  then
      F.i n
    else
      F'.i (n - (F.k )),

  n_orig := fun j =>
  if hj : j < F.k then
    eqToHom (by simp [if_pos (Nat.le_of_lt hj)]) ≫ F.n_orig ⟨j, hj⟩ ≫
      eqToHom (Eq.symm (dif_pos hj))
  else
    if heq : j = F.k then
    eqToHom (by
      by_cases h : j ≤ F.k
      { have hval : ↑j = F.k := heq
        rw [hval]
        by_cases  h1 : F.k ≤ F.k
        {simp}
        {simp } }
      {simp
       exfalso
       apply h
       rw [heq]}) ≫
         F.a ≫
         eqToHom compat ≫
         F'.n_orig ⟨0, by
             have hpos : 0 < F'.k := by
               have hj_sub : ↑j < F.k + F'.k := j.2
               rw [heq] at hj_sub
               exact lt_of_add_lt_add_left hj_sub
             exact hpos⟩
         ≫ eqToHom (by
            by_cases h : j ≤ F.k
            {have hval : ↑j = F.k := heq
             simp
             rw [hval]
             by_cases  h1 : F.k ≤ F.k
             {simp}
             {simp}
             }
            {simp
             exfalso
             apply h
             rw [heq]}
                )
   else    -- j > F.k
       eqToHom (by
       by_cases h : j < F.k
       { simp at h
         exfalso
         contradiction}
       { by_cases h0 :  ↑j ≤ F.k
         { have eqj : ↑j = F.k := le_antisymm h0 (le_of_not_gt hj)
           contradiction}
         { simp[h0] } }  ) ≫ F'.n_orig ⟨j - (F.k), by
                                     have hpos : F.k < ↑j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm heq)
                                     have hgfr : ↑j < F.k + F'.k := j.2
                                     have hsub : ↑j - F.k < F'.k := by
                                        have hpos_nat : F.k < j.val := hpos
                                        have hgfr_nat : j.val < F.k + F'.k := j.2
                                        have hgfz_nat : j.val - F.k < F'.k := by
                                          rw[AddLECancellable.tsub_lt_iff_left]
                                          {exact hgfr_nat}
                                          {intro a b c
                                           exact Nat.le_of_add_le_add_left c}
                                          {have hgo: F.k ≤ ↑j := by exact le_of_lt hpos
                                           exact hgo
                                          }
                                        exact hgfz_nat
                                     exact hsub  ⟩    ≫ eqToHom (by
                                                    by_cases hgp: (if h : ↑j < F.k then true else false)
                                                    {simp[hj]}
                                                    {simp[hj]}),

  n_dom := by
    intro j
    by_cases h: j < F.k
    { simp [h]
      have hx : ↑j + 1 ≤ F.k := Nat.succ_le_of_lt h
      simp[hx]
      have hgds : Z.dom (F.i ↑j) = F.Xs (↑j + 1) := by simp[F.n_dom ⟨j, by
                                                               have hj : ↑j < F.k := Nat.lt_of_succ_le hx
                                                               exact hj  ⟩]
      exact hgds                                                        }
    { simp[h]
      by_cases abs:  ↑j + 1 ≤ F.k
      {exfalso
       contradiction}
      {simp[abs]
       have htr :  Z.dom (F'.i (↑j - F.k)) = F'.Xs ((↑j - F.k)+1):=  by simp[F'.n_dom ⟨(↑j - F.k), by sorry  ⟩] --use j : { j // j < F.k + F'.k }
       simp[htr]
       have hjk : F.k ≤ ↑j := Nat.le_of_not_lt h
       have hsub : ↑j - F.k + 1 = ↑j + 1 - F.k := by sorry --trivial
       simp[hsub]}},





  n_cod := by
         intro j
         by_cases ppz : ↑j < F.k
         { simp [ppz]
           have hgc : Z.cod (F.i ↑j) = F.Ys ↑j := by simp[F.n_cod ⟨j, by exact ppz ⟩]
           exact hgc
         }
         { simp[ppz]
           have erer : Z.cod (F'.i (↑j - F.k)) = F'.Ys (↑j - F.k) := by simp[F'.n_cod ⟨(↑j - F.k), by sorry ⟩] --use j : { j // j < F.k + F'.k }
           exact erer},

  n_in_N := by sorry -- use sieve property: its stabel by precomposition

  a:= if ha : (F'.k)=0  then
      eqToHom (by
    by_cases h : F.k + F'.k ≤ F.k
    {
      have F'_le_zero : F'.k ≤ 0 := Nat.le_of_add_le_add_left h
      have F'_eq_zero : F'.k = 0 := Nat.eq_zero_of_le_zero F'_le_zero
      simp[h]
      simp[F'_eq_zero]
    }
    { exfalso
      have hsum : F.k + F'.k > F.k := Nat.lt_of_not_le h
      apply h
      have sf: F'.k >0 := Nat.lt_of_add_lt_add_left hsum
      have gi : F'.k ≠ 0 := by sorry  ---use sf
      contradiction
    }) ≫ F.a ≫ eqToHom (by
           simp[ha]
           exact compat
           ) ≫ F'.a ≫ eqToHom (by
             by_cases h : F.k + F'.k + 1 ≤ F.k
             {exfalso
              linarith
               }
             {simp[h]
              simp[ha]}
               )
    else
      eqToHom (by
         by_cases  h : F.k + F'.k ≤ F.k
         {exfalso
          have eui : F'.k >0 := by exact Nat.pos_of_ne_zero ha
          linarith}
         {simp[h]})≫ F'.a ≫ eqToHom (by
                             by_cases h : F.k + F'.k ≤ F.k
                             {exfalso
                              have eui : F'.k >0 := by exact Nat.pos_of_ne_zero ha
                              linarith}
                             {by_cases h1 : F.k + F'.k + 1 ≤ F.k
                              {exfalso
                               linarith
                               }
                              {simp[h1]
                               have likj:   F'.k + 1  =F.k + F'.k + 1 - F.k := by sorry -- trivial f-f=0
                               simp[likj]}
                              }          ),


  a_dom := by sorry }

lemma fraction_lemma (F F' : Fraction Z)  (compat : F.Xs (F.k + 1) = F'.Xs 0):
  F'.Xs (F'.k + 1) =
     (composition Z F F' compat).Xs
       ( (composition Z F F' compat).k +1):= by
        simp [composition]
        by_cases h : F.k + F'.k + 1 ≤ F.k
        { simp [h]
          exfalso
          linarith }
        { simp [h]
          have likj:   F'.k + 1  =F.k + F'.k + 1 - F.k := by sorry  -- trivial f-f=0}
          simp[likj]    }






lemma fraction_in_loc_full_comp (F F' : Fraction Z)  (compat : F.Xs (F.k + 1) = F'.Xs 0):
  fraction_in_loc_full Z F ≫
   eqToHom (congrArg (objEquiv (CenterMorphismProperty Z)) compat) ≫
    fraction_in_loc_full Z F' =
     eqToHom (by
     simp only [objEquiv_apply]
     sorry) ≫
      fraction_in_loc_full Z (composition Z F F' compat) ≫
       eqToHom (by sorry)  := by
            sorry


def prescr : MorphismProperty (CenterMorphismProperty Z).Localization := fun X Y f =>
       ∃ (F : Fraction Z), f = eqToHom (by sorry) ≫ fraction_in_loc_full Z F ≫ eqToHom (by sorry)

def prescr_id_mem : ∀ X : (CenterMorphismProperty Z).Localization, prescr Z (𝟙 X) := by sorry

def prescr_comp_mem : ∀ {X Y P : (CenterMorphismProperty Z).Localization}
    {f : X ⟶ Y} {g : Y ⟶ P}, prescr Z f → prescr Z g → prescr Z (f ≫ g) := by sorry


instance prescr_multiplicative : MorphismProperty.IsMultiplicative (prescr Z) where
  id_mem := by
   --prescr_id_mem
   sorry
  comp_mem := by
  --prescr_comp_mem
    sorry


def Dil := WideSubcategory  (prescr Z)


def functor_dil_to_loc : Dil Z  ⥤ (CenterMorphismProperty Z).Localization :=
  wideSubcategoryInclusionFunctor (prescr Z)

lemma functor_dil_to_loc : faithful := by sorry


/-- Functor from C to DilZ -/
def functor_cat_to_dil : C ⥤ Dil Z where
  obj X := { obj := X }
  map {X Y} f := { use mor_fra }
  id_map X :=
  map_comp {X Y Z} f g :=



def is_in_imag (D: Cat ) (F: C ⥤ D) (f : Σ X Y : D, X ⟶ Y) : Prop :=
  ∃ i : Z.I, f = ⟨F.obj (Z.dom i), F.obj (Z.cod i), F.map (Z.mor i)⟩


def CenterimagProperty (D: Cat ) (Funct: C ⥤ D) : MorphismProperty D :=
    fun X Y f => is_in_imag Z D Funct ⟨X, Y, f⟩

def image_Sieve (D : Cat)  (Funct : C ⥤ D) (i : Z.I) :
    Sieve (Funct.obj (Z.cod i)) :=
  Sieve.functorPushforward Funct (Z.N i)

def image_mor_sieve (D : Cat) (Funct : C ⥤ D) (i : Z.I) :
    CategoryTheory.Sieve (Funct.obj (Z.cod i)) :=
  CategoryTheory.Sieve.generateSingleton (Funct.map (Z.mor i))


lemma triangle (Z: Center C) :  (CenterMorphismProperty Z).Q =
  functor_cat_to_dil Z ≫ functor_dil_to_loc Z := by sorry

lemma facto_exists (D: Cat ) (Funct: C ⥤ D)
  (reg: Faithful ((CenterimagProperty Z D Funct).Q)) (i : Z.I) (n : (Z.N i).arrows)
  (he :   image_Sieve Z D Funct i ≤ image_mor_sieve Z D Funct i)  :
  ∃ b : Funct.obj dom n → Funct.obj dom Z.mor ∧ Funct.hom n = b ≫ Funct.hom Z.mor i := by sorry


lemma facto_unique (D: Cat ) (Funct: C ⥤ D)
  (reg: Faithful ((CenterimagProperty Z D Funct).Q)) (i : Z.I) (n : (Z.N i).arrows)
  (he :   image_Sieve Z D Funct i ≤ image_mor_sieve Z D Funct i)
   (b : Funct.obj dom n → Funct.obj dom Z.mor ∧ Funct.hom n = b ≫ Funct.hom Z.mor i)
    (b': Funct.obj dom n → Funct.obj dom Z.mor ∧ Funct.hom n = b' ≫ Funct.hom Z.mor i) :b=b' := by
        sorry



theorem univ_prop (D: Cat ) (F: C ⥤ D)  (reg: Faithful ((CenterimagProperty Z D F).Q))
  (hs : ∀ i : Z.I,  image_Sieve Z D F i ≤ image_mor_sieve Z D F i) :
  ∃! (G : Dil Z ⥤ D), F ⋙ G = functor_cat_to_dil Z  := by
   -- adapt the proof in case of dilatations of rings in the Proj file
    sorry



/-
def inv_in_loc (i : Z.I) :
  ((LocalizationFunctor Z).obj (Z.cod i) ⟶ (LocalizationFunctor Z).obj (Z.dom i)) :=
  Localization.Construction.wInv (Z.mor i) ⟨i, rfl⟩ -/



/--/
lemma triangle (Z: Center C) :  (CenterMorphismProperty Z).Q =
  functor_cat_to_dil Z ≫ functor_dil_to_loc Z := by sorry

lemma facto_exists (Z: Center C)  (i : Z.I) (n : (Z.N i).arrows) :
  ∃ b : Dil dom n → Dil dom Z.mor ∧ n = b ≫ Z.d i := by
        sorry

lemma facto_unique (Z: Center C)  (i : Z.I) (n : (Z.N i).arrows) (b, b': dom n → dom Z.mor i) :
  (hb: ) (hb': ) : b=b':= by
        sorry
-/
