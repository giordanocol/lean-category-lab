import Mathlib
import CategoryTheory.Categories

universe u₁ v₁ u₂ v₂ u₃ v₃

structure MyFunctor
    (C : Type u₁)
    (D : Type u₂)
    [catC : MyCategory C]
    [catD : MyCategory D] where

  obj : C → D

  map :
    {X Y : C} →
    catC.Hom X Y →
    catD.Hom (obj X) (obj Y)

  map_id :
    {X : C} →
    map (catC.id : catC.Hom X X)
      =
    (catD.id : catD.Hom (obj X) (obj X))

  map_comp :
    {X Y Z : C} →
    (f : catC.Hom X Y) →
    (g : catC.Hom Y Z) →
    map (catC.comp f g)
      =
    catD.comp (map f) (map g)

def MyIdFunctor
    (C : Type u₁)
    [catC : MyCategory C]:
    MyFunctor C C where

  obj := fun X => X

  map := fun f => f

  map_id := by
    intro X
    rfl

  map_comp := by
    intro X Y Z f g
    rfl

def MyFunctor.comp
    {C : Type u₁}
    {D : Type u₂}
    {E : Type u₃}
    [catC : MyCategory C]
    [catD : MyCategory D]
    [catE : MyCategory E]
    (G : MyFunctor D E)
    (F : MyFunctor C D) :
    MyFunctor C E where

  obj := fun X => G.obj (F.obj X)

  map := fun f => G.map (F.map f)

  map_id := by
    intro X
    rw [F.map_id]
    rw [G.map_id]

  map_comp := by
    intro X Y Z f g
    rw [F.map_comp]
    rw [G.map_comp]


open CategoryTheory

#check Functor
#check Functor.id
#check Functor.comp

section MathlibFunctor

universe u v

variable {C: Type u} {D : Type v}
variable [Category C] [Category D]

variable (F : C ⥤ D)

#check F.obj
#check F.map

example (X : C) : D :=
 F.obj X

example {X Y : C} (f : X ⟶ Y) :
    F.obj X ⟶ F.obj Y :=
  F.map f

end MathlibFunctor
