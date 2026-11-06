import Mathlib

theorem algebra_248403 (x0 : ℝ) (hx0 : |x0| > Real.sqrt 2) (A B C : ℝ × ℝ)
    (hA : A = (x0, x0 ^ 2)) (hB : B = (x0 - Real.sqrt 2, (x0 - Real.sqrt 2) ^ 2))
    (hC : C = (x0 + Real.sqrt 2, (x0 + Real.sqrt 2) ^ 2)) :
    ∃ y, B.1 * y + C.1 * (y - x0 ^ 2) = 0 := by
  use ( (x0 + Real.sqrt 2 ) * x0 / 2 )
  simp only [hB, hC]
  have hx0_ne_zero : x0 ≠ 0 := by
    by_contra h
    have h1 : x0 = (0 : ℝ) := h
    have h2 : |x0| = 0 := by
      rw [h1]
      norm_num [abs_of_nonneg]
    have h3 : |x0| > Real.sqrt 2 := hx0
    rw [h2] at h3 
    have h4 : Real.sqrt 2 > 0 := by 
      positivity
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  field_simp [(show (x0 : ℝ) ≠ 0 by exact hx0_ne_zero ), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num ) ]
  <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]