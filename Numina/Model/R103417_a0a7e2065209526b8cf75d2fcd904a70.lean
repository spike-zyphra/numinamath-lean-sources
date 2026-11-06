import Mathlib

theorem algebra_748 {m n : ℝ} (hn : n ≠ m) (h1 : m^2 = n + 2) (h2 : n^2 = m + 2) :
    m^3 - 2 * m * n + n^3 = -2 := by
  have h3 : m ^ 2 - n ^ 2 = n - m := by
    linarith
  have h4 : (m - n) * (m + n + 1) = 0 := by
    have h5 : m ^ 2 - n ^ 2 = n - m := h3
    have h6 : m ^ 2 - n ^ 2 = (m - n) * (m + n) := by ring
    rw [h6] at h5
    have h7 : (m - n) * (m + n) = n - m := by linarith [h5]
    have h8 : (m - n) * (m + n + 1) = 0 := by
      nlinarith [h7]
    exact h8
  cases' (mul_eq_zero.mp h4) with h9 h10
  · -- Case where m - n = 0
    exfalso
    apply hn
    linarith
  · -- Thus m + n + 1 = 0, so m + n = -1
    have h11 : m + n = -1 := by linarith [h10]
    have h12 : m * n = -1 := by
      have h13 : m ^ 2 + n ^ 2 = 3 := by
        nlinarith [h1, h2, h11]
      nlinarith [sq_nonneg (m - n), h13, h11]
    have h14 : m ^ 3 + n ^ 3 = -4 := by
      have h15 : m ^ 3 + n ^ 3 = (m + n) ^ 3 - 3 * (m * n) * (m + n) := by ring
      rw [h15, h11, h12]
      norm_num
    nlinarith [h14, h12]