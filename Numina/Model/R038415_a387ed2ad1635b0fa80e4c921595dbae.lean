import Mathlib

theorem number_theory_281814 (x : ℝ) (hx : x = √(3 + √2) + √(3 - √2)) :
    x = √(6 + 2 * √7) := by
  rw [hx]
  have h1 : (√(3 + √2) + √(3 - √2)) ^ 2 = 6 + 2 * √7 := by
    have h2 : (√(3 + √2)) ^ 2 = 3 + √2 := by
      rw [Real.sq_sqrt]
      positivity
    have h3 : (√(3 - √2)) ^ 2 = 3 - √2 := by
      rw [Real.sq_sqrt]
      have h4 : 0 ≤ (3 - √2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
      linarith
    have h5 : (√(3 + √2) : ℝ) * (√(3 - √2) : ℝ) = Real.sqrt 7 := by
      have h6 : (√(3 + √2) : ℝ) * (√(3 - √2) : ℝ) = Real.sqrt ((3 + √2) * (3 - √2)) := by
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        )]
      have h7 : (3 + √2) * (3 - √2) = (7 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      rw [h7] at h6
      linarith
    calc
      (√(3 + √2) + √(3 - √2)) ^ 2
      = (√(3 + √2)) ^ 2 + (√(3 - √2)) ^ 2 + 2 * ((√(3 + √2) : ℝ) * (√(3 - √2) : ℝ)) := by ring
      _ = (3 + √2) + (3 - √2) + 2 * ((√(3 + √2) : ℝ) * (√(3 - √2) : ℝ)) := by
        rw [h2, h3]
      _ = (3 + √2) + (3 - √2) + 2 * (Real.sqrt 7) := by
        rw [h5]
      _ = 6 + 2 * Real.sqrt 7 := by
        ring_nf
  have h2 : (√(6 + 2 * √7) ) ^ 2 = 6 + 2 * √7 := by
    rw [Real.sq_sqrt]
    positivity
  have h3 : √(3 + √2) + √(3 - √2) ≥ 0 := by
    positivity
  have h4 : √(6 + 2 * √7) ≥ 0 := by
    positivity
  have h5 : (√(3 + √2) + √(3 - √2)) = √(6 + 2 * √7) := by
    nlinarith [h1, h2, Real.sqrt_nonneg (6 + 2 * √7), Real.sqrt_nonneg (3 + √2), Real.sqrt_nonneg (3 - √2)]
  linarith [h5]