import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_296918 {S T : Set (ℝ × ℝ)}
  (hS : S = {(x, y) | x * y > 0}) (hT : T = {(x, y) | 0 < x ∧ 0 < y}) :
  S ∪ T = S := by
  ext ⟨x, y⟩
  simp only [hS, hT, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · -- Assume (x * y > 0) ∨ (0 < x ∧ 0 < y), prove x * y > 0
    rintro (h | ⟨hx, hy⟩)
    · -- Case 1: Assume h : x * y > 0, prove x * y > 0
      exact h
    · -- Case 2: Assume hx : 0 < x, hy : 0 < y, prove x * y > 0
      have h1 : x * y > 0 := mul_pos hx hy
      exact h1
  · -- Assume x * y > 0, prove (x * y > 0) ∨ (0 < x ∧ 0 < y)
    intro h
    left
    exact h