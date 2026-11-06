import Mathlib

open Real

lemma lemma_1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x - y) * (Real.sqrt (2 * (x ^ 2 + y ^ 2)) - (x + y)) ≤ (x - y) ^ 2 := by
  by_cases h : x ≥ y
  ·
    have h1 : 0 ≤ x - y := by linarith
    have h2 : Real.sqrt (2 * (x ^ 2 + y ^ 2)) ≤ 2 * x := by
      have h3 : (Real.sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 ≤ (2 * x) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)),
          Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity)]
      have h4 : 0 ≤ Real.sqrt (2 * (x ^ 2 + y ^ 2)) := Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2))
      nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity)]
    nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity)]
  ·
    have h1 : x - y < 0 := by linarith
    have h2 : Real.sqrt (2 * (x ^ 2 + y ^ 2)) ≥ 2 * x := by
      have h3 : (Real.sqrt (2 * (x ^ 2 + y ^ 2))) ^ 2 ≥ (2 * x) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)),
          Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity)]
      have h4 : 0 ≤ Real.sqrt (2 * (x ^ 2 + y ^ 2)) := Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2))
      nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity)]
    nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity)]


theorem algebra_224112 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x - y) * sqrt (x ^ 2 + y ^ 2) + (y - z) * sqrt (y ^ 2 + z ^ 2) +
     (z - x) * sqrt (z ^ 2 + x ^ 2) + sqrt 2) /
    ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 + 2) ≤ 1 / sqrt 2 := by
  have h1 : 0 < sqrt 2 := Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by linarith)
  have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)
  have h8 : ((x - y) * Real.sqrt (x ^ 2 + y ^ 2) + (y - z) * Real.sqrt (y ^ 2 + z ^ 2) + (z - x) * Real.sqrt (z ^ 2 + x ^ 2) + Real.sqrt 2) * Real.sqrt 2 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 + 2 := by
    have h77 : Real.sqrt (2 * (x ^ 2 + y ^ 2)) = Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) := by
      have h12 : 2 * (x ^ 2 + y ^ 2) ≥ 0 := by positivity
      have h77 : Real.sqrt (2 * (x ^ 2 + y ^ 2)) = Real.sqrt (2) * Real.sqrt (x ^ 2 + y ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      exact h77
    have h78 : Real.sqrt (2 * (y ^ 2 + z ^ 2)) = Real.sqrt 2 * Real.sqrt (y ^ 2 + z ^ 2) := by
      have h12 : 2 * (y ^ 2 + z ^ 2) ≥ 0 := by positivity
      have h78 : Real.sqrt (2 * (y ^ 2 + z ^ 2)) = Real.sqrt (2) * Real.sqrt (y ^ 2 + z ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      exact h78
    have h79 : Real.sqrt (2 * (z ^ 2 + x ^ 2)) = Real.sqrt 2 * Real.sqrt (z ^ 2 + x ^ 2) := by
      have h12 : 2 * (z ^ 2 + x ^ 2) ≥ 0 := by positivity
      have h79 : Real.sqrt (2 * (z ^ 2 + x ^ 2)) = Real.sqrt (2) * Real.sqrt (z ^ 2 + x ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      exact h79
    have h3 : (x - y) * (Real.sqrt (2 * (x ^ 2 + y ^ 2)) - (x + y)) ≤ (x - y) ^ 2 := by
      apply lemma_1 x y hx hy
    have h4 : (y - z) * (Real.sqrt (2 * (y ^ 2 + z ^ 2)) - (y + z)) ≤ (y - z) ^ 2 := by
      apply lemma_1 y z hy hz
    have h5 : (z - x) * (Real.sqrt (2 * (z ^ 2 + x ^ 2)) - (z + x)) ≤ (z - x) ^ 2 := by
      apply lemma_1 z x hz hx
    rw [h77] at h3
    rw [h78] at h4
    rw [h79] at h5
    nlinarith [Real.sqrt_nonneg (2 * (x ^ 2 + y ^ 2)), Real.sqrt_nonneg (2 * (y ^ 2 + z ^ 2)), Real.sqrt_nonneg (2 * (z ^ 2 + x ^ 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 * (x ^ 2 + y ^ 2) : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (2 * (y ^ 2 + z ^ 2) : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (2 * (z ^ 2 + x ^ 2) : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
  have h9 : ((x - y) * Real.sqrt (x ^ 2 + y ^ 2) + (y - z) * Real.sqrt (y ^ 2 + z ^ 2) + (z - x) * Real.sqrt (z ^ 2 + x ^ 2) + Real.sqrt 2) / ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 + 2) ≤ (1 / Real.sqrt 2 : ℝ) := by
    have h99 : ((x - y) * Real.sqrt (x ^ 2 + y ^ 2) + (y - z) * Real.sqrt (y ^ 2 + z ^ 2) + (z - x) * Real.sqrt (z ^ 2 + x ^ 2) + Real.sqrt 2) * Real.sqrt 2 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 + 2 := h8
    have h10 : ((x - y) * Real.sqrt (x ^ 2 + y ^ 2) + (y - z) * Real.sqrt (y ^ 2 + z ^ 2) + (z - x) * Real.sqrt (z ^ 2 + x ^ 2) + Real.sqrt 2) / ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 + 2) ≤ (1 / Real.sqrt 2 : ℝ) := by
      have h11 : Real.sqrt 2 > 0 := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by linarith), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
    linarith
  simpa using h9