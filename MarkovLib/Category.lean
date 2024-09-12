import Mathlib.CategoryTheory.Monoidal.Braided.Basic

open CategoryTheory
open CategoryTheory.Iso
open MonoidalCategory
open SymmetricCategory
open BraidedCategory

open Category

universe v u

def inner_swap {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
               (X Y : C) : (X ⊗ X) ⊗ (Y ⊗ Y) ≅ (X ⊗ Y) ⊗ (X ⊗ Y) :=
  calc
    (X ⊗ X) ⊗ (Y ⊗ Y) ≅ X ⊗ (X ⊗ (Y ⊗ Y)) := by exact α_ X X (Y ⊗ Y)
                    _ ≅ X ⊗ ((X ⊗ Y) ⊗ Y) := by exact (refl X ⊗ (symm (α_ X Y Y)))
                    _ ≅ X ⊗ ((Y ⊗ X) ⊗ Y) := by exact (refl X ⊗ (β_ X Y ⊗ refl Y))
                    _ ≅ X ⊗ (Y ⊗ (X ⊗ Y)) := by exact (refl X ⊗ (α_ Y X Y))
                    _ ≅ (X ⊗ Y) ⊗ (X ⊗ Y) := by exact (symm (α_ X _ _))


namespace CategoryTheory

class MarkovCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] where
  /-- copy map -/
  copy (X : C) : X ⟶ X ⊗ X
  /-- delete map -/
  del (X : C) : X ⟶ 𝟙_C

  /-- laws -/
  copy_unit_l (X : C) : copy X ≫ (del X ⊗ 𝟙 X) ≫ (λ_ X).hom = 𝟙 X
  copy_assoc (X : C) : copy X ≫ (𝟙 X ⊗ copy X) = copy X ≫ (copy X ⊗ 𝟙 X) ≫ (α_ X X X).hom
  copy_comm (X : C) : copy X ≫ (β_ X X).hom = copy X
  copy_tensor (X Y : C) : copy (X ⊗ Y) = (copy X ⊗ copy Y) ≫ (inner_swap X Y).hom
  del_unique {X : C} (f : X ⟶ 𝟙_C) : f = del X

  -- copy_unit_r is derivable



open MarkovCategory

attribute [simp] copy_unit_l copy_assoc copy_comm copy_tensor del_unique


/- Some basic lemmas -/

section BasicLemmas

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MarkovCategory C]

lemma braid_del (X : C) :
  (β_ X X).hom ≫ (𝟙 X ⊗ del X) ≫ (ρ_ X).hom = (del X ⊗ 𝟙 X) ≫ (λ_ X).hom
  := by
    rw [← assoc, ← braiding_naturality, assoc, braiding_rightUnitor]

@[simp]
lemma copy_unit_r (X : C) : copy X ≫ (𝟙 X ⊗ del X) ≫ (ρ_ X).hom = 𝟙 X := by
  rw [← copy_comm, Category.assoc, braid_del, copy_unit_l]

-- prove some lemmas
lemma semicartesian {X : C} (f g : X ⟶ 𝟙_C) : f = g := by
  rw [del_unique f, ← del_unique g]

@[simp]
lemma del_natural {X Y : C} (f : X ⟶ Y) : f ≫ del Y = del X := by
  apply semicartesian

end BasicLemmas

/- Determinism -/

section Determinism

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MarkovCategory C]

-- definitions
def deterministic {X Y : C} (f : X ⟶ Y) := f ≫ copy Y = copy X ≫ (f ⊗ f)

lemma comp_deterministic {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  deterministic f -> deterministic g -> deterministic (f ≫ g) := by
  intros p q
  unfold deterministic at *
  simp only [assoc, tensor_comp]
  rw [q,← Category.assoc,p]
  simp only [assoc]

lemma id_deterministic {X : C} : deterministic (𝟙 X) := by
  unfold deterministic
  simp

lemma del_deterministic {X : C} : deterministic (del X) := by
  unfold deterministic
  apply (cancel_iso_hom_right_assoc _ _ _ _ (ρ_ (𝟙_ C))).mp
  apply semicartesian

lemma copy_deterministic {X : C} : deterministic (copy X) := by
  unfold deterministic
  rw [copy_tensor]
  unfold inner_swap
  simp only [instTransIso_trans, trans_assoc,
    trans_hom, tensorIso_hom, refl_hom, symm_hom, id_tensorHom, tensorHom_id]
  sorry

end Determinism


/- Almost sure equality -/


section AlmostSure

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MarkovCategory C]

def almost_surely_equal {A X Y : C} (p : A ⟶ X) (f g : X ⟶ Y) :=
  p ≫ copy X ≫ (𝟙 X ⊗ f) = p ≫ copy X ≫ (𝟙 X ⊗ g)

end AlmostSure
