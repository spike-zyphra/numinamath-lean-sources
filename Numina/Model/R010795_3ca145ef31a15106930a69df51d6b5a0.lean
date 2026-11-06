import Mathlib

open Real

theorem algebra_149797 :
    sqrt (2 - sqrt 3) * sqrt (2 - sqrt (2 - sqrt 3)) *
    sqrt (2 - sqrt (2 - sqrt (2 - sqrt 3))) * sqrt (2 + sqrt (2 - sqrt (2 - sqrt 3))) = 1 := by
  have h1 : 0 ≤ (2 - sqrt 3 : ℝ) := by
    have h2 : sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_iff] <;> norm_num
      <;> linarith [show (3 : ℝ) ≤ (4 : ℝ) by norm_num]
    linarith [show (0 : ℝ) ≤ sqrt 3 by positivity]
  have h2 : 0 ≤ (2 - sqrt (2 - sqrt 3) : ℝ) := by
    have h3 : sqrt (2 - sqrt 3) ≤ 2 := by
      have : sqrt (2 - sqrt 3) ≤ sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg 3, h1])
      have h4 : sqrt (2 : ℝ) ≤ 2 := by
        rw [Real.sqrt_le_iff] <;> norm_num
      linarith
    linarith [Real.sqrt_nonneg (2 - sqrt 3), h3]
  have h3 : 0 ≤ (2 - sqrt (2 - sqrt (2 - sqrt 3)) : ℝ) := by
    have h4 : sqrt (2 - sqrt (2 - sqrt 3)) ≤ 2 := by
      have : sqrt (2 - sqrt (2 - sqrt 3)) ≤ sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg (2 - sqrt 3), h2])
      have h5 : sqrt (2 : ℝ) ≤ 2 := by
        rw [Real.sqrt_le_iff] <;> norm_num
      linarith
    linarith [Real.sqrt_nonneg (2 - sqrt (2 - sqrt 3)), h4]
  have h4 : 0 ≤ (2 + sqrt (2 - sqrt (2 - sqrt 3)) : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 - sqrt (2 - sqrt 3)), Real.sq_sqrt (show 0 ≤ (2 - sqrt (2 - sqrt 3) : ℝ) by linarith [h2, Real.sqrt_nonneg (2 - sqrt 3)])]
  have h5 : sqrt (2 - sqrt 3) * sqrt (2 - sqrt (2 - sqrt 3)) *
    sqrt (2 - sqrt (2 - sqrt (2 - sqrt 3))) * sqrt (2 + sqrt (2 - sqrt (2 - sqrt 3))) =
    sqrt ((2 - sqrt 3) * (2 - sqrt (2 - sqrt 3)) * (2 - sqrt (2 - sqrt (2 - sqrt 3))) * (2 + sqrt (2 - sqrt (2 - sqrt 3)))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [h5]
  have h6 : (2 - sqrt 3) * (2 - sqrt (2 - sqrt 3)) * (2 - sqrt (2 - sqrt (2 - sqrt 3))) * (2 + sqrt (2 - sqrt (2 - sqrt 3))) = 1 := by
    have h7 : (2 - sqrt (2 - sqrt (2 - sqrt 3))) * (2 + sqrt (2 - sqrt (2 - sqrt 3))) = 2 + sqrt (2 - sqrt 3) := by
      have h8 : (sqrt (2 - sqrt (2 - sqrt 3)))^2 = 2 - sqrt (2 - sqrt 3) := by
        rw [Real.sq_sqrt]
        linarith [show 0 ≤ (2 - sqrt (2 - sqrt 3) : ℝ) by linarith [h3, Real.sqrt_nonneg (2 - sqrt (2 - sqrt 3))]]
      nlinarith [h8, Real.sqrt_nonneg (2 - sqrt (2 - sqrt 3))]
    have h9 : (2 - sqrt (2 - sqrt 3)) * (2 + sqrt (2 - sqrt 3)) = 2 + sqrt 3 := by
      have h10 : (sqrt (2 - sqrt 3))^2 = 2 - sqrt 3 := by
        rw [Real.sq_sqrt]
        linarith [show 0 ≤ (2 - sqrt 3 : ℝ) by linarith [h1, Real.sqrt_nonneg 3]]
      nlinarith [h10, Real.sqrt_nonneg (2 - sqrt 3), Real.sqrt_nonneg 3]
    calc
      (2 - sqrt 3) * (2 - sqrt (2 - sqrt 3)) * (2 - sqrt (2 - sqrt (2 - sqrt 3))) * (2 + sqrt (2 - sqrt (2 - sqrt 3)))
          = (2 - sqrt 3) * (2 - sqrt (2 - sqrt 3)) * ((2 - sqrt (2 - sqrt (2 - sqrt 3))) * (2 + sqrt (2 - sqrt (2 - sqrt 3)))) := by ring
      _ = (2 - sqrt 3) * (2 - sqrt (2 - sqrt 3)) * (2 + sqrt (2 - sqrt 3)) := by rw [h7]
      _ = (2 - sqrt 3) * ((2 - sqrt (2 - sqrt 3)) * (2 + sqrt (2 - sqrt 3))) := by ring
      _ = (2 - sqrt 3) * (2 + sqrt 3) := by rw [h9]
      _ = 1 := by
        have h11 : (sqrt 3)^2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        nlinarith [h11, Real.sqrt_nonneg 3]
  rw [h6]
  simp