import Mathlib

open Real

theorem algebra_17028 : 1 / (1 / (Real.sqrt 2 + 1) + 2 / (Real.sqrt 3 - 1)) = Real.sqrt 3 - Real.sqrt 2 := by
  have h1 : 0 < Real.sqrt 2 := by
    positivity
  have h2 : 0 < Real.sqrt 3 := by
    positivity
  have h3 : Real.sqrt 2 + 1 ≠ 0 := by
    positivity
  have h4 : Real.sqrt 3 - 1 ≠ 0 := by
    have h5 : Real.sqrt 3 > 1 := by
      have h6 : 1 < (Real.sqrt 3) := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith
    nlinarith
  have h5 : 1 / (Real.sqrt 2 + 1) = Real.sqrt 2 - 1 := by
    field_simp [(show Real.sqrt 2 + 1 ≠ 0 by positivity)]
    <;> ring_nf <;> norm_num
    <;> ring
  have h6 : 2 / (Real.sqrt 3 - 1) = Real.sqrt 3 + 1 := by
    field_simp [(show Real.sqrt 3 - 1 ≠ 0 by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h4
      ])]
    <;> ring_nf <;> norm_num
    <;> ring
  have h7 : 1 / (Real.sqrt 2 + 1) + 2 / (Real.sqrt 3 - 1) = Real.sqrt 2 + Real.sqrt 3 := by
    rw [h5, h6]
    ring
  rw [h7]
  have h8 : 0 < Real.sqrt 2 + Real.sqrt 3 := by positivity
  field_simp [(show Real.sqrt 2 + Real.sqrt 3 ≠ 0 by positivity)]
  <;> ring_nf <;> norm_num
  <;> ring