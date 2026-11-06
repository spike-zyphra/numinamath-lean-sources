import Mathlib

open Real

theorem algebra_324198 (x : ℝ) (hx : x ≥ -3) (h : sqrt (3 + sqrt (3 + sqrt (3 + x))) = x) :
    x = (1 + sqrt 13) / 2 := by
  have h1 : 0 ≤ x := by
    by_contra h1
    push_neg at h1
    have h2 : sqrt (3 + sqrt (3 + sqrt (3 + x))) ≥ 0 := Real.sqrt_nonneg (3 + sqrt (3 + sqrt (3 + x)))
    nlinarith [h, Real.sqrt_nonneg (3 + sqrt (3 + sqrt (3 + x))), Real.sqrt_nonneg (3 + sqrt (3 + x)), Real.sqrt_nonneg (3 + x)]
  have h2 : 3 + sqrt (3 + sqrt (3 + x)) = x^2 := by
    calc
      3 + sqrt (3 + sqrt (3 + x)) = (sqrt (3 + sqrt (3 + sqrt (3 + x)))) ^ 2 := by
        rw [Real.sq_sqrt]
        have h3 : 0 ≤ 3 + sqrt (3 + sqrt (3 + x)) := by
          have h4 : sqrt (3 + sqrt (3 + x)) ≥ 0 := Real.sqrt_nonneg (3 + sqrt (3 + x))
          nlinarith [Real.sqrt_nonneg (3 + x)]
        linarith
      _ = x^2 := by
        rw [h]
  have h3 : sqrt (3 + sqrt (3 + x)) = x^2 - 3 := by
    nlinarith [Real.sqrt_nonneg (3 + sqrt (3 + sqrt (3 + x))), Real.sqrt_nonneg (3 + sqrt (3 + x)), Real.sqrt_nonneg (3 + x)]
  have h4 : x^2 ≥ 3 := by
    have h5 : sqrt (3 + sqrt (3 + x)) ≥ 0 := Real.sqrt_nonneg (3 + sqrt (3 + x))
    nlinarith [h3, Real.sqrt_nonneg (3 + sqrt (3 + x)), Real.sqrt_nonneg (3 + x)]
  have h5 : 3 + sqrt (3 + x) = (x^2 - 3) ^ 2 := by
    calc
      3 + sqrt (3 + x) = (sqrt (3 + sqrt (3 + x))) ^ 2 := by
        rw [Real.sq_sqrt]
        have h6 : 0 ≤ 3 + sqrt (3 + x) := by
          have h6 : sqrt (3 + x) ≥ 0 := Real.sqrt_nonneg (3 + x)
          nlinarith
        linarith
      _ = (x^2 - 3) ^ 2 := by
        have h7 : sqrt (3 + sqrt (3 + x)) = x^2 - 3 := by
          linarith [h3]
        rw [h7]
  have h6 : sqrt (3 + x) = (x^2 - 3) ^ 2 - 3 := by
    nlinarith [Real.sqrt_nonneg (3 + x), Real.sqrt_nonneg (3 + sqrt (3 + x)), Real.sqrt_nonneg (3 + sqrt (3 + sqrt (3 + x)))]
  have h7 : sqrt (3 + x) ≥ 0 := Real.sqrt_nonneg (3 + x)
  have h9 : 3 + x = ((x^2 - 3) ^ 2 - 3) ^ 2 := by
    calc
      3 + x = (sqrt (3 + x)) ^ 2 := by
        rw [Real.sq_sqrt]
        have h3x : 0 ≤ 3 + x := by
          nlinarith [h1]
        linarith
      _ = ((x^2 - 3) ^ 2 - 3) ^ 2 := by
        rw [h6]
  have h10 : (x - (1 + Real.sqrt 13) / 2) * (x - (1 - Real.sqrt 13) / 2) = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - 3 - x), sq_nonneg ((x ^ 2 - 3) ^ 2 - 3 - x), sq_nonneg (x ^ 2 - x - 3), Real.sqrt_pos.mpr (show 0 < (13 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by linarith), Real.sqrt_nonneg (13 : ℝ)]
  cases' (mul_eq_zero.mp h10) with h11 h12
  · -- Case $x = \frac{1 + \sqrt{13}}{2}$.
    have h13 : x = (1 + Real.sqrt 13) / 2 := by
      nlinarith
    linarith
  · -- Case $x = \frac{1 - \sqrt{13}}{2}$.
    nlinarith [Real.sqrt_nonneg 13, Real.sqrt_nonneg (3 + sqrt (3 + sqrt (3 + x))), Real.sqrt_nonneg (3 + sqrt (3 + x)), Real.sqrt_nonneg (3 + x), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by linarith)]