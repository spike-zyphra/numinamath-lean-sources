import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314738 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (h : a + b = 3) :
  sqrt (a^2 + 4) + sqrt (b^2 + 25) ≥ sqrt 58 ∧
  (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 3 ∧
    sqrt (a^2 + 4) + sqrt (b^2 + 25) = sqrt 58) := by

  have h1 : sqrt (a^2 + 4) + sqrt (b^2 + 25) ≥ sqrt 58 := by
    have h2 : (sqrt (a^2 + 4) + sqrt (b^2 + 25)) ^ 2 ≥ 58 := by
      have h3 : (sqrt (a^2 + 4) + sqrt (b^2 + 25)) ^ 2 =
        (sqrt (a^2 + 4)) ^ 2 + (sqrt (b^2 + 25)) ^ 2 + 2 * (sqrt (a^2 + 4) * sqrt (b^2 + 25)) := by
        ring
      rw [h3]
      have h4 : (sqrt (a^2 + 4)) ^ 2 = a^2 + 4 := Real.sq_sqrt (by positivity)
      have h5 : (sqrt (b^2 + 25)) ^ 2 = b^2 + 25 := Real.sq_sqrt (by positivity)
      rw [h4, h5]
      nlinarith [sq_nonneg (sqrt (a^2 + 4) - sqrt (b^2 + 25)), sq_nonneg (a - b), sq_nonneg (a - 6 / 7), sq_nonneg (b - 15 / 7),
        Real.sqrt_nonneg (a^2 + 4), Real.sqrt_nonneg (b^2 + 25),
        sq_nonneg (a - b), h,
        mul_nonneg (Real.sqrt_nonneg (a^2 + 4)) (Real.sqrt_nonneg (b^2 + 25))
        ]
    have h6 : sqrt ((sqrt (a^2 + 4) + sqrt (b^2 + 25)) ^ 2) ≥ sqrt (58 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h7 : sqrt ((sqrt (a^2 + 4) + sqrt (b^2 + 25)) ^ 2) = sqrt (a^2 + 4) + sqrt (b^2 + 25) := by
      rw [Real.sqrt_sq (show 0 ≤ (sqrt (a^2 + 4) + sqrt (b^2 + 25)) by
        linarith [Real.sqrt_nonneg (a^2 + 4), Real.sqrt_nonneg (b^2 + 25)])]
    linarith [h6, h7]

  have h3 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 3 ∧ sqrt (a^2 + 4) + sqrt (b^2 + 25) = sqrt 58 := by
    use (6 / 7), (15 / 7)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    have h8 : sqrt ((6 / 7 : ℝ) ^ 2 + 4) + sqrt ((15 / 7 : ℝ) ^ 2 + 25) = sqrt 58 := by
      have h1 : sqrt ((6 / 7 : ℝ) ^ 2 + 4) = (2 * sqrt 58) / 7 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num [mul_pow]
      have h2 : sqrt ((15 / 7 : ℝ) ^ 2 + 25) = (5 * sqrt 58) / 7 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num [mul_pow]
      rw [h1, h2]
      linarith [Real.sqrt_nonneg 58]
    linarith [h8]

  constructor
  · exact h1
  · exact h3