import Mathlib

theorem algebra_187836 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h₀ : x + y = 13) (h₁ : Real.logb 4 x + Real.logb 4 y = 1 + Real.logb 4 10) :
    (x = 5 ∧ y = 8) ∨ (x = 8 ∧ y = 5) := by

  have h2 : Real.logb 4 x + Real.logb 4 y = Real.logb 4 (x * y) := by
    rw [Real.logb_mul (by linarith) (by linarith)]

  rw [h2] at h₁

  -- Convert the value 1 to Real.logb 4 4 and use logarithm properties
  have h3 : (1 : ℝ) = Real.logb 4 (4 : ℝ) := by
    rw [Real.logb_self_eq_one]
    all_goals norm_num
    all_goals norm_num
    -- Real.logb_self_eq_one(4)

  have h5 : (1 : ℝ) + Real.logb 4 (10 : ℝ) = Real.logb 4 (40 : ℝ) := by
    calc
      (1 : ℝ) + Real.logb 4 (10 : ℝ)
          = Real.logb 4 (4 : ℝ) + Real.logb 4 (10 : ℝ) := by rw [h3]
      _ = Real.logb 4 (4 * 10) := by rw [Real.logb_mul (by norm_num) (by norm_num)]
      _ = Real.logb 4 (40 : ℝ) := by norm_num

  rw [h5] at h₁

  have h6 : x * y = (40 : ℝ) := by
    have h7 : x * y > 0 := by positivity
    have h8 : (40 : ℝ) > 0 := by norm_num
    have h9 : Real.logb 4 (x * y) = Real.logb 4 (40 : ℝ) := h₁
    have h10 : x * y = (40 : ℝ) := by
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h7) (Set.mem_Ioi.mpr h8) h9
    exact h10
  -- Now h6: x * y = 40.

  -- Solve using the quadratic.
  have h11 : x^2 - 13 * x + 40 = 0 := by
    have eq1 : y = 13 - x := by
      linarith
    rw [eq1] at h6
    nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x * y), h₀, h6]

  have h12 : (x - 5) * (x - 8) = 0 := by
    nlinarith [h11]

  cases' (mul_eq_zero.1 h12) with h13 h14
  · -- Case where x = 5, then y = 8
    have hx5 : x = 5 := by linarith
    have hy8 : y = 8 := by linarith [h₀, hx5]
    left
    exact ⟨hx5, hy8⟩
  · -- Case where x = 8, then y = 5
    have hx8 : x = 8 := by linarith
    have hy5 : y = 5 := by linarith [h₀, hx8]
    right
    exact ⟨hx8, hy5⟩