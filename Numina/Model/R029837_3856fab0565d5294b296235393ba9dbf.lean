import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_215394 (x y : ℝ) :
  |Real.sin x - Real.sin y| ≤ |x - y| := by
  have h1 : Real.sin x - Real.sin y = 2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2) := by
    rw [show (x : ℝ) = ( (x + y) / 2 + (x - y) / 2 ) by ring]
    rw [show (y : ℝ) = ( (x + y) / 2 - (x - y) / 2 ) by ring]
    rw [Real.sin_add, Real.sin_sub]
    ring_nf
    <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring
  have h2 : |Real.sin x - Real.sin y| = |(2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2))| := by 
    rw [h1]
  have h3 : |(2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2))| = 2 * |Real.cos ((x + y) / 2)| * |Real.sin ((x - y) / 2)| := by
    calc
      |(2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2))| = |(2)| * |(Real.cos ((x + y) / 2))| * |(Real.sin ((x - y) / 2))| := by
        simp [abs_mul]
      _ = 2 * |Real.cos ((x + y) / 2)| * |Real.sin ((x - y) / 2)| := by
        norm_num
  have h4 : |Real.cos ((x + y) / 2)| ≤ 1 := by 
    apply abs_cos_le_one
  have h5 : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := by 
    apply abs_sin_le_abs
  have h6 : |Real.sin x - Real.sin y| = 2 * |Real.cos ((x + y) / 2)| * |Real.sin ((x - y) / 2)| := by
    rw [h2, h3]
  rw [h6]
  have h7 : 2 * |Real.cos ((x + y) / 2)| * |Real.sin ((x - y) / 2)| ≤ 2 * |Real.sin ((x - y) / 2)| := by
    have h8 : |Real.cos ((x + y) / 2)| ≤ 1 := h4
    have h9 : |Real.sin ((x - y) / 2)| ≥ 0 := by positivity
    nlinarith [abs_nonneg (Real.cos ((x + y) / 2)), abs_nonneg (Real.sin ((x - y) / 2))]
  have h8 : 2 * |Real.sin ((x - y) / 2)| ≤ |x - y| := by
    have h5' : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := h5
    have h9 : |x - y| = 2 * |(x - y) / 2| := by
      calc
        |x - y| = |2 * ((x - y) / 2)| := by
          ring_nf
        _ = |(2:ℝ)| * |((x - y) / 2)| := by
          rw [abs_mul]
        _ = (2:ℝ) * |((x - y) / 2)| := by
          norm_num
        _ = 2 * |(x - y) / 2| := by
          ring
    linarith [abs_nonneg (Real.sin ((x - y) / 2)), abs_nonneg ((x - y) / 2)]
  linarith [h7, h8]