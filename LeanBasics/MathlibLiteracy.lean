import Mathlib

/-!
# Week 08 — Mathlib Literacy

Goal:
Find relevant Mathlib API without knowing exact lemma names in advance.

Tools practiced:
- #check
- #print
- #synth
- exact?
- apply?
- simp?
- Go to Definition
- Find References
- source
-/

-- 1. Transitivity of ≤
example (x y z : ℝ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  exact le_trans hxy hyz

-- 2. Intersection is contained in the left set
example {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  exact Set.inter_subset_left

-- 3. Intersection is contained in the right set
example {α : Type} (A B : Set α) : A ∩ B ⊆ B := by
  exact Set.inter_subset_right

-- 4. A is contained in A ∪ B
example {α : Type} (A B : Set α) : A ⊆ A ∪ B := by
  exact Set.subset_union_left

-- 5. B is contained in A ∪ B
example {α : Type} (A B : Set α) : B ⊆ A ∪ B := by
  exact Set.subset_union_right

-- 6. Functions preserve equality
example {α β : Type} (f : α → β) {x y : α} (h : x = y) : f x = f y := by
  exact congrArg f h

-- 7. Symmetry of equality
example {α : Type} {x y : α} (h : x = y) : y = x := by
  exact h.symm

-- 8. Transitivity of equality
example {α : Type} {x y z : α} (hxy : x = y) (hyz : y = z) : x = z := by
  exact hxy.trans hyz

-- 9. min a b ≤ a
example (a b : ℝ) : min a b ≤ a := by
  exact min_le_left a b

-- 10. min a b ≤ b
example (a b : ℝ) : min a b ≤ b := by
  exact min_le_right a b

-- 11. a ≤ max a b
example (a b : ℝ) : a ≤ max a b := by
  exact le_max_left a b

-- 12. b ≤ max a b
example (a b : ℝ) : b ≤ max a b := by
  exact le_max_right a b

-- 13. Absolute value is nonnegative
example (x : ℝ) : 0 ≤ |x| := by
  exact abs_nonneg x

-- 14. Membership in intersection implies membership in the left set
example {α : Type} {A B : Set α} {x : α} (hx : x ∈ A ∩ B) : x ∈ A := by
  exact hx.1

-- 15. Membership in intersection implies membership in the right set
example {α : Type} {A B : Set α} {x : α} (hx : x ∈ A ∩ B) : x ∈ B := by
  exact hx.2

-- 16. Membership in A implies membership in A ∪ B
example {α : Type} {A B : Set α} {x : α} (hx : x ∈ A) : x ∈ A ∪ B := by
  exact Or.inl hx

-- 17. Membership in B implies membership in A ∪ B
example {α : Type} {A B : Set α} {x : α} (hx : x ∈ B) : x ∈ A ∪ B := by
  exact Or.inr hx

-- 18. x ≤ y implies x < y or x = y
example (x y : ℝ) (h : x ≤ y) : x < y ∨ x = y := by
  exact lt_or_eq_of_le h

-- 19. Transitivity of subset
example {α : Type} {A B C : Set α}
    (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  exact hAB.trans hBC

-- 20. Preimage preserves intersection
example {α β : Type} (f : α → β) (A B : Set β) :
    f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := by
  exact Set.preimage_inter

/-!
## Small API inspection examples
-/

#check zero_add
#check add_zero
#check one_mul
#check mul_one
#check sq_nonneg

#print Std.IsPreorder.le_trans

#synth LinearOrder ℝ
