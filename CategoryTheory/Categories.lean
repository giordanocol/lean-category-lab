import Mathlib

universe u v

class MyCategory (C : Type u) where
  Hom : C → C → Type v
  id: {X : C} → Hom X X
  comp: {X Y Z : C} → Hom X Y → Hom Y Z → Hom X Z
  assoc:
    {W X Y Z : C} →
    (f: Hom W X) →
    {g: Hom X Y} →
    {h: Hom Y Z} →
    comp ( comp f g) h = comp f (comp g h)
  id_comp :
    {X Y: C} →
    (f : Hom X Y ) →
    comp id f = f
  comp_id :
    {X Y : C} →
    (f: Hom X Y) →
    comp f id = f

instance typeCategory : MyCategory (Type u) where
  Hom X Y := X → Y
  id := fun x => x
  comp f g := fun x => g (f x)
  assoc := by
    intro W X Y Z f g h
    rfl
  id_comp := by
    intro X Y f
    rfl
  comp_id := by
    intro X Y f
    rfl

instance preorederCategory (P : Type u) [Preorder P] : MyCategory where
  Hom x y := x ≤ y
  id := le_rifl
  comp hxy hyz := le_trans hxy hyz

  assoc := by
   intro W X Y Z f g h
   rfl

  id_comp := by
    intro X Y f
    rfl

  comp_id := by
    intro X Y f
    rfl
