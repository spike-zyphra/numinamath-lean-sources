import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_247319 (x1 : ℝ) (x : ℝ) (h : |x - x1| ≤ 1 / 100) :
    |sin x - sin x1| ≤ 1 / 100 := by 
  have h1 : |sin x - sin x1| ≤ |x - x1| := by 
    have h2 : sin x - sin x1 = 2 * cos ((x + x1) / 2) * sin ((x - x1) / 2) := by 
      rw [show x = (x + x1) / 2 + (x - x1) / 2 by ring]
      rw [show x1 = (x + x1) / 2 - (x - x1) / 2 by ring]
      rw [sin_add, sin_sub]
      ring
    rw [h2]
    have h3 : |(2 * cos ((x + x1) / 2) * sin ((x - x1) / 2))| ≤ 2 * |sin ((x - x1) / 2)| := by 
      have h4 : |(2 * cos ((x + x1) / 2) * sin ((x - x1) / 2))| = 2 * |cos ((x + x1) / 2)| * |sin ((x - x1) / 2)| := by 
        calc 
          |(2 * cos ((x + x1) / 2) * sin ((x - x1) / 2))| = |(2 * cos ((x + x1) / 2)) * sin ((x - x1) / 2)| := by ring_nf
          _ = |(2 * cos ((x + x1) / 2))| * |sin ((x - x1) / 2)| := by 
            simp [abs_mul]
          _ = 2 * |cos ((x + x1) / 2)| * |sin ((x - x1) / 2)| := by
            have h5 : |(2 * cos ((x + x1) / 2))| = 2 * |cos ((x + x1) / 2)| := by
              simp [abs_mul]
            rw [h5]
      have h7 : |cos ((x + x1) / 2)| ≤ 1 := by 
        apply abs_cos_le_one
      have h8 : 2 * |cos ((x + x1) / 2)| ≤ 2 := by 
        linarith [h7]
      have h9 : 2 * |cos ((x + x1) / 2)| * |sin ((x - x1) / 2)| ≤ 2 * |sin ((x - x1) / 2)| := by 
        nlinarith [abs_nonneg (sin ((x - x1) / 2)), h7]
      linarith [h4, h9]
    have h4 : |sin ((x - x1) / 2)| ≤ |(x - x1) / 2| := by 
      apply abs_sin_le_abs 
    have h5 : 2 * |sin ((x - x1) / 2)| ≤ |x - x1| := by 
      have h6 : |sin ((x - x1) / 2)| ≤ |(x - x1) / 2| := h4 
      have h7 : 2 * |sin ((x - x1) / 2)| ≤ 2 * |(x - x1) / 2| := by 
        linarith [h6]
      have h8 : 2 * |(x - x1) / 2| = |x - x1| := by 
        have h9 : |(x - x1) / 2| = |x - x1| / 2 := by 
          field_simp [abs_div]
        rw [h9]
        ring
      linarith [h7, h8]
    linarith [h3, h5]
  have h2 : |x - x1| ≤ 1 / 100 := h 
  linarith [h1, h2]