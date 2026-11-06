import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_216315 :
  {x : ℝ | x^3 + 1 > x^2 + x} = Ioo (-1) 1 ∪ Ioi 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · -- Assume x^3 + 1 > x^2 + x, prove x ∈ (-1, 1) ∪ (1, ∞)
    intro h
    have h1 : x ^ 3 + 1 - (x ^ 2 + x) > 0 := by linarith
    have h2 : x ^ 3 + 1 - (x ^ 2 + x) = (x + 1) * (x - 1) ^ 2 := by
      ring
    rw [h2] at h1
    by_cases h3 : x < 1
    · -- If x < 1, prove x ∈ (-1, 1)
      have h4 : x > -1 := by
        nlinarith [sq_nonneg (x - 1)]
      left
      constructor
      · -- Show -1 < x
        linarith
      · -- Show x < 1
        linarith
    · -- If x ≥ 1
      have h3 : x ≥ 1 := by linarith
      have h5 : x > 1 := by
        by_contra h
        push_neg at h
        have h6 : x = 1 := by nlinarith
        rw [h6] at h1
        nlinarith
      right
      simp at *
      all_goals try linarith
  · -- Assume x ∈ (-1, 1) ∪ (1, ∞), prove x^3 + 1 > x^2 + x
    rintro (h | h)
    · -- Case x ∈ (-1, 1)
      rcases h with ⟨h1, h2⟩
      have h3 : x ^ 3 + 1 - (x ^ 2 + x) > 0 := by
        have h4 : (x + 1) * (x - 1) ^ 2 > 0 := by
          apply mul_pos
          all_goals
            nlinarith
        nlinarith
      linarith
    · -- Case x ∈ (1, ∞)
      have h4 : x > 1 := h
      have h3 : x ^ 3 + 1 - (x ^ 2 + x) > 0 := by
        have h4' : (x + 1) * (x - 1) ^ 2 > 0 := by
          apply mul_pos
          all_goals
            nlinarith
        nlinarith
      linarith