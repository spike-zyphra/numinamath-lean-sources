import Mathlib

theorem algebra_226486 {a b : ℝ} (ha : a^2 + 3 * a - 2 = 0) (hb : b + Real.sqrt (b + 1) = 3)
    (ha' : 0 < a) : a + b = 2 := by

  have h1 : 0 ≤ b + 1 := by
    by_contra h
    push_neg at h
    have h2 : b < -1 := by linarith
    have h3 : Real.sqrt (b + 1) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals
        nlinarith
    rw [h3] at hb
    nlinarith

  have h2 : Real.sqrt (b + 1) ≥ 0 := Real.sqrt_nonneg (b + 1)
  have h3_eq : Real.sqrt (b + 1) = 3 - b := by
    nlinarith [hb]

  have h4 : (Real.sqrt (b + 1)) ^ 2 = (3 - b) ^ 2 := by
    rw [h3_eq]

  have h5 : (Real.sqrt (b + 1)) ^ 2 = b + 1 := by
    exact Real.sq_sqrt (by linarith)

  have h6 : b + 1 = (3 - b) ^ 2 := by
    nlinarith [h4, h5]

  have h7 : b^2 - 7 * b + 8 = 0 := by
    nlinarith [h6]

  have h51 : a = (-3 + Real.sqrt 17) / 2 := by
    have h51 : a^2 + 3 * a - 2 = 0 := ha
    have h52 : a^2 + 3 * a - 2 = (a - (-3 + Real.sqrt 17) / 2) * (a - (-3 - Real.sqrt 17) / 2) := by
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    rw [h52] at h51
    cases' mul_eq_zero.1 h51 with h53 h54
    · -- a = (-3 + Real.sqrt 17) / 2
      linarith
    · -- a = (-3 - Real.sqrt 17) / 2
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]

  have h51' : b = (7 - Real.sqrt 17) / 2 := by
    have h61 : b^2 - 7 * b + 8 = 0 := h7
    have h62 : b^2 - 7 * b + 8 = (b - (7 + Real.sqrt 17) / 2) * (b - (7 - Real.sqrt 17) / 2) := by
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    rw [h62] at h61
    cases' mul_eq_zero.1 h61 with h63 h64
    · -- b = (7 + Real.sqrt 17) / 2
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), h3_eq, Real.sqrt_nonneg (b + 1)]
    · -- b = (7 - Real.sqrt 17) / 2
      linarith

  have h11 : a + b = 2 := by
    nlinarith [h51, h51']

  exact h11