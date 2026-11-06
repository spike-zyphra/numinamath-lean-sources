import Mathlib

theorem algebra_11136 : IsLeast {c > 0 | ∀ x y : ℝ, 0 ≤ x ∧ 0 ≤ y → Real.sqrt (x * y) + c * |x - y| ≥ (x + y) / 2} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set.
    constructor
    · norm_num
    · -- Show that for all x, y, the inequality holds
      intro x y h
      rcases h with ⟨hx, hy⟩
      have h1 : Real.sqrt (x * y) ≥ 0 := by positivity
      by_cases h2 : x ≥ y
      · -- If x ≥ y, then |x - y| = x - y
        have h3 : |x - y| = x - y := by
          rw [abs_of_nonneg]
          linarith
        rw [h3]
        nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ x * y by nlinarith), sq_nonneg (Real.sqrt (x * y) - y), sq_nonneg (x - y), Real.mul_self_sqrt (show 0 ≤ x * y by nlinarith)]
      · -- If y > x, then |x - y| = y - x
        have h3 : |x - y| = y - x := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        rw [h3]
        nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ x * y by nlinarith), sq_nonneg (Real.sqrt (x * y) - x), sq_nonneg (y - x), Real.mul_self_sqrt (show 0 ≤ x * y by nlinarith)]
  · -- Show that 1/2 is the least element in the set
    intro c ⟨hc, h⟩
    have h2 := h 1 0 (by constructor <;> norm_num)
    norm_num [abs_of_nonneg, abs_of_nonpos] at h2
    all_goals linarith