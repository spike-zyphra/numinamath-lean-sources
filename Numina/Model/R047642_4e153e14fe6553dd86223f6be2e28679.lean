import Mathlib

open Real

theorem algebra_247394 : ∑' n : ℕ, ((sqrt 2 + 1) / (sqrt 2 - 1)) * ((sqrt 2 - 1) / sqrt 2) ^ n = 4 + 3 * sqrt 2 := by
  have h1 : sqrt 2 > 1 := by
    have h1 : sqrt 2 > Real.sqrt 1 := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    have h2 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
    linarith [h1, h2]

  have h2 : sqrt 2 - 1 > 0 := by linarith [h1]

  have h3 : sqrt 2 > 0 := by positivity

  have h4 : |(sqrt 2 - 1) / sqrt 2| < 1 := by
    have h5 : (sqrt 2 - 1) / sqrt 2 < 1 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h6 : -1 < (sqrt 2 - 1) / sqrt 2 := by
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    apply abs_lt.mpr
    constructor <;> linarith

  have h5 : ∑' n : ℕ, ((sqrt 2 + 1) / (sqrt 2 - 1)) * ((sqrt 2 - 1) / sqrt 2) ^ n =
      (sqrt 2 + 1) / (sqrt 2 - 1) / (1 - (sqrt 2 - 1) / sqrt 2) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · exact h4

  rw [h5]

  have h7 : 1 - (sqrt 2 - 1) / sqrt 2 = 1 / sqrt 2 := by
    field_simp [h3]
    all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

  rw [h7]

  have h8 : (sqrt 2 + 1) / (sqrt 2 - 1) / (1 / sqrt 2) = (sqrt 2 + 1) * sqrt 2 / (sqrt 2 - 1) := by
    field_simp [h2, h3, show sqrt 2 - 1 ≠ 0 by linarith]

  rw [h8]

  have h12 : (sqrt 2 + 1) * sqrt 2 = 2 + sqrt 2 := by
    have h9 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2]

  rw [h12]

  have h7 : (2 + sqrt 2) / (sqrt 2 - 1) = 4 + 3 * sqrt 2 := by
    have h9 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    field_simp [show sqrt 2 - 1 ≠ 0 by linarith, Real.sqrt_nonneg 2]
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (sqrt 2 ^ 2 - 2)]

  field_simp at h7 ⊢
  all_goals nlinarith