import Mathlib

open Real

theorem algebra_311907 : (sqrt 3 + 2 * sqrt 5 + sqrt 7) / (sqrt 15 + sqrt 21 + sqrt 35 + 5) =
    ((sqrt 7 - sqrt 3) / 2) := by
  have h1 : sqrt 15 = sqrt 3 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt 21 = sqrt 3 * sqrt 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : sqrt 35 = sqrt 5 * sqrt 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
  have h5 : sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
  have h6 : sqrt 7 ≥ 0 := Real.sqrt_nonneg 7
  have h7 : sqrt 15 ≥ 0 := Real.sqrt_nonneg 15
  have h8 : sqrt 21 ≥ 0 := Real.sqrt_nonneg 21
  have h9 : sqrt 35 ≥ 0 := Real.sqrt_nonneg 35
  have h13 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h14 : sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h15 : sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h11 : (sqrt 3 + 2 * sqrt 5 + sqrt 7) / (sqrt 15 + sqrt 21 + sqrt 35 + 5) = ((sqrt 7 - sqrt 3) / 2) := by
    have h13 : sqrt 15 = sqrt 3 * sqrt 5 := h1
    have h14 : sqrt 21 = sqrt 3 * sqrt 7 := h2
    have h15 : sqrt 35 = sqrt 5 * sqrt 7 := h3
    field_simp [(show sqrt 15 + sqrt 21 + sqrt 35 + 5 ≠ 0 by positivity)]
    rw [show sqrt 15 = sqrt 3 * sqrt 5 by linarith [h1]]
    rw [show sqrt 21 = sqrt 3 * sqrt 7 by linarith [h2]]
    rw [show sqrt 35 = sqrt 5 * sqrt 7 by linarith [h3]]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sqrt_nonneg 7, 
                  sq_nonneg (sqrt 3 - sqrt 5), sq_nonneg (sqrt 7 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 7), 
                  mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5), 
                  mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 7), 
                  mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7)
                ]
  exact h11