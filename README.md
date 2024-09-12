# MarkovLib

We formalize some of the theory of [Markov categories](https://arxiv.org/pdf/1908.07021) in Lean4/Mathlib.

The central definition is
```lean
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
```

Now we can make definitions and prove lemmas

```lean
def deterministic {X Y : C} (f : X ⟶ Y) := f ≫ copy Y = copy X ≫ (f ⊗ f)

lemma comp_deterministic {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  deterministic f -> deterministic g -> deterministic (f ≫ g) := by
  intros p q
  unfold deterministic at *
  simp only [assoc, tensor_comp]
  rw [q,← Category.assoc,p]
  simp only [assoc]

def almost_surely_equal {A X Y : C} (p : A ⟶ X) (f g : X ⟶ Y) :=
  p ≫ copy X ≫ (𝟙 X ⊗ f) = p ≫ copy X ≫ (𝟙 X ⊗ g)

-- ...
```

# Use

You'll need
1. [Lean4](https://leanprover-community.github.io/install/linux.html)
2. the VS-Code extension [vscode-lean4](https://github.com/leanprover/vscode-lean4)

To run this project, clone the repository into a folder. Enter this folder and run

``lake exe cache get``

to download mathlib4. Then launch VSCode (`code .`) and step through the individual files, such as `Category.lean`.