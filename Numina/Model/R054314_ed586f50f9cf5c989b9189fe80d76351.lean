import Mathlib

theorem algebra_309315 {x : ℝ} (h : (Real.sqrt 3 + 1) * x = Real.sqrt 3 - 1) :
    x^4 - 5 * x^3 + 6 * x^2 - 5 * x + 4 = 3 := by

  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
  have h4 : Real.sqrt 3 + 1 ≠ 0 := by linarith [h3]

  have hx : x = (2 - Real.sqrt 3) := by
    have eq1 : (Real.sqrt 3 + 1) * x = Real.sqrt 3 - 1 := h
    have eq2 : x = (Real.sqrt 3 - 1) / (Real.sqrt 3 + 1) := by
      field_simp [(show Real.sqrt 3 + 1 ≠ 0 by linarith [h3])]
      <;> nlinarith
      <;> field_simp [(show Real.sqrt 3 + 1 ≠ 0 by linarith [h3])]
      <;> nlinarith
    rw [eq2]
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by linarith [h3]), h2]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    <;> nlinarith
    <;> ring_nf <;> norm_num
    <;> nlinarith
  
  rw [hx]

  nlinarith [sq_nonneg (Real.sqrt 3), sq_nonneg ((Real.sqrt 3) ^ 2), sq_nonneg (Real.sqrt 3 - 2), sq_nonneg (Real.sqrt 3 - 1), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), h2]