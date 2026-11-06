import Mathlib

theorem algebra_243074 (a b c d : ℝ) (ha : a ≥ 0) (hd : d ≥ 0) (hdc : d ≤ c) (hcb : c ≤ b)
    (hba : b ≤ a) (h : (a^2 + b^2 + c^2 + d^2) / (a + b + c + d)^2 = 3 / 8) :
    (a + c) / (b + d) ≤ 3 := by
  have h1 : a + b + c + d ≠ 0 := by
    by_contra h1
    have h2 : (a^2 + b^2 + c^2 + d^2) / (a + b + c + d)^2 = 0 := by
      rw [h1]
      norm_num
    linarith
  have h2 : a + b + c + d > 0 := by
    have h3 : a + b + c + d > 0 := by
      have h1' : a + b + c + d ≠ 0 := h1
      by_contra h3
      have h4 : a + b + c + d ≤ 0 := by nlinarith
      have h1 : a + b + c + d = 0 := by
        linarith
      contradiction
    linarith
  have h_eq : 8 * (a^2 + b^2 + c^2 + d^2) = 3 * (a + b + c + d)^2 := by
    have h2' : (a + b + c + d)^2 ≠ 0 := by
      have : a + b + c + d ≠ 0 := h1
      intro h'
      apply h1
      nlinarith
    field_simp [h2'] at h
    nlinarith
  by_cases hbd : b + d > 0
  · -- Case $b + d > 0$. We can multiply both sides by $b + d$.
    have h3 : a + c ≤ 3 * (b + d) := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), h_eq, mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcb), mul_nonneg (sub_nonneg.mpr hcb) (sub_nonneg.mpr hdc)]
    have h4 : (a + c) / (b + d) ≤ (3 * (b + d)) / (b + d) := by
      apply (div_le_div_right hbd).mpr
      nlinarith
    have h5 : (3 * (b + d)) / (b + d) = (3 : ℝ) := by
      field_simp [show b + d ≠ 0 by linarith]
      all_goals linarith
    linarith [h4, h5, h3]
  · -- Case $b + d \leq 0$. Since $b \geq 0$ and $d \geq 0$, we must have $b = 0$ and $d = 0$.
    have h5 : b = 0 := by
      nlinarith
    have h6 : d = 0 := by
      nlinarith
    have h7 : a + c = 0 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), h_eq, mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcb), mul_nonneg (sub_nonneg.mpr hcb) (sub_nonneg.mpr hdc)]
    have h8 : b + d = 0 := by
      nlinarith
    have h9 : (a + c) / (b + d) = 0 := by
      rw [h8]
      norm_num
      all_goals nlinarith
    nlinarith [h9, h7]