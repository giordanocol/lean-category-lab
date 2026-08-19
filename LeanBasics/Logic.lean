import Mathlib

theorem identity_implication (P : Prop) : P → P := by
  intro h
  exact h

theorem identity_implication_term (P : Prop) : P → P :=
  fun h => h

theorem swap_and (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨hP , hQ⟩
  constructor
  exact hQ
  exact hP

theorem swap_or (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  exact Or.inr hP
  exact Or.inl hQ

theorem exists_self (α : Type) (a : α) : ∃ x : α,x = a := by
  exists a
