import Mathlib

theorem succ_injective : Function.Injective Nat.succ := by
  intro a b h
  exact Nat.succ.inj h

theorem id_surjective : Function.Surjective (fun x : Nat => x) := by
  intro y
  exact ⟨y,rfl⟩

theorem composition_example
  (f : Nat → Nat) (g : Nat → Nat) (x : Nat) :
  (g ∘ f) x = g (f x) := by
  rfl

theorem image_example
  (f : Nat → Nat) (s: Set Nat) (x : Nat)
  (hx : x ∈ s) :
  f x ∈ f '' s := by
  exact ⟨x, hx, rfl⟩

theorem preimage_example
  (f : Nat → Nat) (s : Set Nat) (x : Nat)
  (hx : f x ∈ s) :
  x ∈ f⁻¹' s := by
  exact hx
