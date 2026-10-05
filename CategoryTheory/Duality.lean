import Mathlib.CategoryTheory.Opposites

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
variable {A B D : C}

example (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).op = g.op ≫ f.op := by
  rfl

example
    (q : Opposite.op A ⟶  Opposite.op B)
    (r : Opposite.op B ⟶  Opposite.op A):
    (q ≫ r).unop = r.unop ≫ q.unop := by
  rfl

example (f : A ⟶ B) :
    f.op.unop = f := by
  rfl

example (q : Opposite.op A ⟶ Opposite.op B) :
    q.unop.op = q := by
  rfl

example {E : C}
    (f : A ⟶ B) (g : A ⟶ D)
    (h : B ⟶ E) (k : D ⟶ E)
    (comm : f ≫ h = g ≫ k) :
    h.op ≫ f.op = k.op ≫ g.op := by
  exact congrArg (fun t => t.op) comm
