import Mathlib

theorem add_zero_example (n : Nat) : n + 0 = n := by
  rfl

theorem rewrite_example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw[h]

theorem calc_example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  calc
    a = b := h₁
    _ = c := h₂

theorem funext_example (f g : Nat → Nat)
  (h : ∀ x , f x = g x) : f = g := by
  funext x
  exact h x

theorem ext_example (f g :  Nat → Nat)
  (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x

/-!
### Definitional vs propositional equality

Definitional equality means that two expressions reduce to the same term by computation.
In those cases, `rfl` can close the goal directly.

Propositional equality is an explicit proposition of the form `a = b`.
Its proof may require rewriting, transitivity, extensionality, or other lemmas.
-/
