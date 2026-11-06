import Mathlib

theorem algebra_15145 {m : ℝ} (h : (m - 4) ^ 3 = (1 / 8) ^ (-1 : ℤ)) : m = 6 := by
  have h1 : (m - 4) ^ 3 = 8 := by
    have h1 : (1 / 8 : ℝ) ^ (-1 : ℤ) = 8 := by
      norm_num
    rw [h1] at h
    exact h
  have h2 : m - 4 = 2 := by
    have h2 : m - 4 = 2 := by
      have h2 : (m - 4) ^ 3 - 8 = 0 := by linarith
      have h3 : (m - 4) ^ 3 - 8 = (m - 4 - 2) * ((m - 4) ^ 2 + 2 * (m - 4) + 4) := by ring
      rw [h3] at h2
      cases' (mul_eq_zero.mp h2) with h4 h5
      · linarith
      · have h6 : (m - 4) ^ 2 + 2 * (m - 4) + 4 > 0 := by
          have h7 : (m - 4) ^ 2 + 2 * (m - 4) + 4 = (m - 4 + 1) ^ 2 + 3 := by ring
          rw [h7]
          have h8 : (m - 4 + 1) ^ 2 ≥ 0 := by
            apply sq_nonneg
          linarith
        linarith
    linarith
  linarith