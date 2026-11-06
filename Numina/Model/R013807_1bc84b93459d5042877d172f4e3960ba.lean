import Mathlib

theorem algebra_204472 (x y : ℝ) (α θ γ : ℝ)
    (h₁ : x = γ * Real.sin ((θ - α) / 2)) (h₂ : y = γ * Real.sin ((θ + α) / 2)) :
    x ^ 2 - 2 * x * y * Real.cos α + y ^ 2 = γ ^ 2 * Real.sin α ^ 2 := by 
  rw [h₁, h₂]
  have h3 : Real.sin ((θ + α) / 2) = Real.sin ((θ - α) / 2) * Real.cos α + Real.cos ((θ - α) / 2) * Real.sin α := by 
    have h4 : (θ + α) / 2 = (θ - α) / 2 + α := by
      ring
    rw [h4]
    rw [Real.sin_add]
    <;> ring
  rw [h3]
  have h4 : Real.sin ((θ - α) / 2) ^ 2 + Real.cos ((θ - α) / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq ((θ - α) / 2)
  ring_nf
  <;> simp [Real.sin_sq, Real.cos_sq, mul_add, mul_sub, add_mul, sub_mul, mul_comm]
  <;> nlinarith [Real.sin_sq_add_cos_sq ((θ - α) / 2), Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin ((θ - α) / 2) * Real.sin α), sq_nonneg (Real.cos ((θ - α) / 2) * Real.sin α), sq_nonneg (Real.sin ((θ - α) / 2) * Real.cos α), sq_nonneg (Real.cos ((θ - α) / 2) * Real.cos α)]