import Mathlib

open Real

theorem algebra_5165 (x y z : ℝ) (h : x + y + z = π) :
  cos x ^ 2 + cos y ^ 2 + cos z ^ 2 + 2 * cos x * cos y * cos z = 1 := by
  have h1 : cos z = -cos (x + y) := by 
    rw [show z = π - (x + y) by linarith [h]]
    rw [cos_pi_sub]
  have h2 : cos z = - (cos x * cos y - sin x * sin y) := by
    rw [h1]
    rw [cos_add]
  have h3 : sin z = sin (x + y) := by 
    rw [show z = π - (x + y) by linarith [h]]
    rw [sin_pi_sub]
  have h4 : sin (x + y) = sin x * cos y + cos x * sin y := by 
    rw [sin_add]
  -- Express cos z ^ 2 in terms of sine and cosine of x and y
  have h5 : cos z ^ 2 = (cos x * cos y - sin x * sin y) ^ 2 := by 
    rw [h2]
    all_goals ring_nf
  -- Express the product 2 * cos x * cos y * cos z
  have h6 : 2 * cos x * cos y * cos z = -2 * cos x * cos y * (cos x * cos y - sin x * sin y) := by
    rw [h2]
    <;> ring_nf
  rw [h5, h6]
  have h7 : cos x ^ 2 + sin x ^ 2 = 1 := by 
    have h7 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    linarith
  have h8 : cos y ^ 2 + sin y ^ 2 = 1 := by 
    have h8 : cos y ^ 2 + sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y
    linarith
  nlinarith [Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y, sq_nonneg (sin x - sin y), sq_nonneg (cos x - cos y), sq_nonneg (sin x), sq_nonneg (sin y)]