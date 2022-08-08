/-
Author: Alex Ghorbani 2022
-/

import category_theory.category.basic
import category_theory.functor.basic
import category_theory.monoidal.category
import category_theory.isomorphism
import category_theory.functor.category
import category_theory.full_subcategory

universes v₁ v₂ u₁ u₂

open category_theory

namespace category_theory

variables (C : Type u₁) [category.{v₁} C] 
          (D : Type u₂) [category.{v₂} D] 

/-!
Dagger Categories

A dagger category is a category C equipped with a function called 
the dagger function such that for every pair of objects A,B in C, the dagger function
sends morphisms A ⟶ B to morphisms B ⟶ A. In addition, the dagger function must satisfy
the following rules:

  for every A in C, dagger (𝟙 A) = 𝟙 A,
  for every W X Y in C and every f : W ⟶ X and g : X ⟶ Y, 
    dagger f ≫ g = dagger g ≫ dagger f,
  for every A B in C and f : A ⟶ B, dagger (dagger f) = f.  
-/

class dagger_category (C : Type u₁) [category.{v₁} C] :=
  (hom_dagger {x y : C} : (x ⟶ y) → (y ⟶ x))
  (id_dagger (x) : hom_dagger (𝟙 x) = 𝟙 x)
  (dagger_involutive {x y} (f : x ⟶ y) : hom_dagger (hom_dagger f) = f)
  (comp_dagger {x y z} (f : x ⟶ y) (g : y ⟶ z) : 
    hom_dagger (f ≫ g) = hom_dagger g ≫ hom_dagger f)


variables [dagger_category C] [dagger_category D]

def is_unitary_morphism {x y : C} (f : x ⟶ y) [is_iso f] : Prop := 
  dagger_category.hom_dagger f = inv f

def is_self_adjoint {x : C} (f : x ⟶ x) : Prop := 
  dagger_category.hom_dagger f = f

/-
A dagger functor is a functor F between dagger categories such that 
  
  for any morphism f : x ⟶ y in the source category C, 
    F (dagger_C f) = dagger_D (F f) 
-/

structure dagger_functor [dagger_category C] [dagger_category D] extends C ⥤ D :=
  (blank {x y : C} (f : x ⟶ y) : 
    map (dagger_category.hom_dagger f) = dagger_category.hom_dagger (map f))

/-
A monoidal dagger category is a dagger category which is also a monoidal category
where furthermore, the tensor product ⊗ respects the dagger function in the
following sense: 
  for any f : x ⟶ y and g : a ⟶ b, dagger (f ⊗ g) = dagger f ⊗ dagger g
-/

class monoidal_dagger_category [dagger_category C] [monoidal_category C] :=
  (tensor_of_morphism {w x y z : C} (f : w ⟶ x) (g : y ⟶ z) : 
    dagger_category.hom_dagger (f ⊗ g) 
    = dagger_category.hom_dagger f ⊗ dagger_category.hom_dagger g)

/-
dagger natural transformations
-/

/-
Category of dagger functors.

The category of dagger functors is a full subcategory of the category of 
functors. Namely, the objects are dagger functors and the morphisms are 
the natural transformations betweeen them
-/

def is_dagger_functor : (C ⥤ D) → Prop := sorry 

def dagger_functor_category (C D : Type*) := category_theory.full_subcategory is_dagger_functor

/-
A braided monoidal dagger category is a monoidal dagger category equipped with a
braiding natural isomorphism that respects the dagger function in the following sense:
  
-/

class braided_monoidal_dagger_category 
  [dagger_category C] [monoidal_category C] [monoidal_dagger_category C]

class symmetric_monoidal_dagger_category 
  [dagger_category C] [monoidal_category C] [monoidal_dagger_category C]
  [braided_monoidal_dagger_category C]

class compact_closed_dagger_category
  [dagger_category C] [monoidal_category C] [monoidal_dagger_category C]
  [braided_monoidal_dagger_category C] [symmetric_monoidal_dagger_category C]

end category_theory