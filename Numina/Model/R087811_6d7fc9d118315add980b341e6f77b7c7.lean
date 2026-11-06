import Mathlib

theorem algebra_9684 (x : ℝ) (y : ℕ) (hy : y > 0) (h : y = (2022 : ℝ) / (x ^ 2 + 10 * x + 66)) :
    y ≤ 49 := by
  have h1 : (x ^ 2 + 10 * x + 66 : ℝ) ≥ 41 := by
    nlinarith [sq_nonneg (x + 5)]
  have h2 : (y : ℝ) = (2022 : ℝ) / (x ^ 2 + 10 * x + 66) := by
    linarith
  have h3 : (y : ℝ) ≤ (2022 / 41 : ℝ) := by 
    have h4 : (x ^ 2 + 10 * x + 66 : ℝ) ≥ (41 : ℝ) := h1
    have h5 : (2022 : ℝ) / (x ^ 2 + 10 * x + 66) ≤ (2022 : ℝ) / (41 : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith
    have h6 : (y : ℝ) = (2022 : ℝ) / (x ^ 2 + 10 * x + 66) := by 
      linarith
    linarith [h6, h5]
  have h4 : y ≤ 49 := by
    by_contra h5
    push_neg at h5
    have h6 : y ≥ 50 := by 
      omega
    have h7 : (y : ℝ) ≥ (50 : ℝ) := by
      exact_mod_cast h6
    have h8 : (x ^ 2 + 10 * x + 66 : ℝ) ≤ (2022 / 50 : ℝ) := by
      have h9 : (y : ℝ) * (x ^ 2 + 10 * x + 66 : ℝ) = (2022 : ℝ) := by 
        have h10 : x^2 + 10 * x + 66 ≠ 0 := by
          by_contra h'
          have : (y : ℝ) = 0 := by 
            rw [h]
            norm_num [h']
          have h5' : (y : ℝ) > 0 := by 
            exact_mod_cast show (y : ℕ) > 0 by linarith [hy]
          linarith
        field_simp [h10] at h ⊢
        nlinarith
      nlinarith [h7, h9]
    nlinarith [h1, h8]
  exact h4