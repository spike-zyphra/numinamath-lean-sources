import Mathlib

theorem algebra_293041 (x y : ℝ) (h : 3 * Real.sin y = 2 * Real.sin y ^ 2 + Real.sin x ^ 2) :
    Real.cos (2 * x) - 2 * Real.sin y ∈ Set.Icc (-2) 1 ∪ {-3} := by
  have h1 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    have h2 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
      rw [Real.cos_two_mul, Real.sin_sq]
      all_goals
        ring
    exact h2
  have h2 : Real.sin x ^ 2 = 3 * Real.sin y - 2 * Real.sin y ^ 2 := by
    nlinarith
  have h3 : Real.cos (2 * x) - 2 * Real.sin y = 4 * Real.sin y ^ 2 - 8 * Real.sin y + 1 := by
    rw [h1]
    rw [h2]
    nlinarith
  have h4 : 0 ≤ Real.sin y := by
    nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.sin y - 1 / 2), sq_nonneg (Real.sin y - 1), Real.sin_sq_le_one x, Real.sin_sq_le_one y, sq_nonneg (Real.sin y ^ 2 - 3 / 4)]
  have h5 : Real.sin y ≤ 1 := by
    apply Real.sin_le_one
  have h6 : Real.sin y ≤ 1 / 2 ∨ Real.sin y = 1 := by
    have h8 : 2 * Real.sin y ^ 2 - 3 * Real.sin y + 1 ≥ 0 := by
      nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.sin y - 1 / 2), sq_nonneg (Real.sin y - 1), Real.sin_sq_le_one x, Real.sin_sq_le_one y, h]
    have h9 : (2 * Real.sin y - 1) * (Real.sin y - 1) ≥ 0 := by
      nlinarith
    by_cases h11 : Real.sin y ≤ 1 / 2
    · left
      nlinarith
    · -- Therefore, Real.sin y > 1/2.
      right
      -- From the previous analysis, either Real.sin y ≤ 1/2 or Real.sin y ≥ 1.
      -- If Real.sin y > 1/2 and Real.sin y ≤ 1, then Real.sin y ∈ (1/2, 1].
      -- But from the previous analysis, Real.sin y either ≤ 1/2 or ≥ 1.
      -- Therefore, Real.sin y must be exactly 1.
      nlinarith [sq_nonneg (Real.sin y - 1), Real.sin_le_one y, sq_nonneg (Real.sin x), sq_nonneg (Real.sin y - 1 / 2), sq_nonneg (Real.sin y - 1), h]
  rw [h3]
  rcases h6 with h7 | h8
  · -- Real.sin y ≤ 1 / 2
    have h11 : Real.sin y ≤ 1 / 2 := h7
    have h10 : -2 ≤ 4 * Real.sin y ^ 2 - 8 * Real.sin y + 1 ∧ 4 * Real.sin y ^ 2 - 8 * Real.sin y + 1 ≤ 1 := by
      constructor
      · -- Proof of -2 ≤ ...
        nlinarith [sq_nonneg (Real.sin y - 1 / 2), sq_nonneg (Real.sin y - 1), Real.sin_le_one y, sq_nonneg (Real.sin y ^ 2 - 1 / 4), h4, h11]
      · -- Proof of ... ≤ 1
        nlinarith [sq_nonneg (Real.sin y - 1 / 2), sq_nonneg (Real.sin y - 1), Real.sin_le_one y, sq_nonneg (Real.sin y ^ 2 - 1 / 4), h4, h11]
    left
    exact h10
  · -- Real.sin y = 1
    have h10 : Real.sin y = 1 := h8
    have h11 : 4 * Real.sin y ^ 2 - 8 * Real.sin y + 1 = -3 := by
      rw [show Real.sin y = (1 : ℝ) by linarith [h10]]
      norm_num
    right
    simp [h11]