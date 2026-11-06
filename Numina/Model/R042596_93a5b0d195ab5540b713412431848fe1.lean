import Mathlib

open Real

theorem algebra_185262 (α : ℝ) :
    cos α + sin α + cos (3 * α) + sin (3 * α) =
    2 * sqrt 2 * cos α * sin (π / 4 + 2 * α) := by
  have h1 : cos (3 * α) = 4 * cos α ^ 3 - 3 * cos α := by 
    rw [cos_three_mul]
    <;> ring_nf <;> norm_num
  have h2 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by 
    rw [sin_three_mul]
    <;> ring_nf <;> norm_num
  have h3 : sin (π / 4 + 2 * α) = sin (π / 4) * cos (2 * α) + cos (π / 4) * sin (2 * α) := by
    rw [sin_add]
  have h4 : sin (π / 4) = sqrt 2 / 2 := by
    rw [sin_pi_div_four]
  have h5 : cos (π / 4) = sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  have h6 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by 
    rw [cos_two_mul]
    all_goals ring_nf <;> norm_num
  have h7 : sin (2 * α) = 2 * sin α * cos α := by
    rw [sin_two_mul]
  -- Now applying the above facts.
  rw [h1, h2, h3, h4, h5, h6, h7]
  have h8 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have ht1 : sqrt 2 ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    linarith
  ring_nf
  <;> simp only [pow_two, mul_add, mul_sub, mul_assoc, add_mul, sub_mul]
  <;> ring_nf
  <;> norm_num [ht1]
  <;> ring_nf
  <;> norm_num [ht1, h8]
  <;> nlinarith [Real.sqrt_nonneg 2, sq_nonneg (sin α), sq_nonneg (cos α), sq_nonneg (sin α - cos α), sq_nonneg (sin α + cos α), sq_nonneg (sin α ^ 2), sq_nonneg (cos α ^ 2), sq_nonneg (sin α ^ 2 - cos α ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]