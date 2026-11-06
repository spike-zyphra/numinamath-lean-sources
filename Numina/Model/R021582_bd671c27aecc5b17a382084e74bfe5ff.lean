import Mathlib

theorem algebra_189186 (α β γ : ℝ) (h : α + β + γ = Real.pi) :
    Real.sin α + Real.sin β + Real.sin γ = 4 * Real.cos (α / 2) * Real.cos (β / 2) * Real.cos (γ / 2) := by
  have h1 : γ = Real.pi - α - β := by linarith
  rw [h1]
  have h2 : Real.sin (Real.pi - α - β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    have h3 : Real.sin (Real.pi - α - β) = Real.sin (α + β) := by
      have h4 : α + β = Real.pi - (Real.pi - α - β) := by ring
      rw [h4]
      rw [Real.sin_pi_sub]
      <;> ring_nf
      <;> simp [Real.sin_pi_sub, Real.cos_pi_sub]
      <;> ring_nf
    rw [h3]
    rw [Real.sin_add]
    <;> ring_nf <;> simp [Real.sin_pi_sub, Real.cos_pi_sub]
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring
  rw [h2]
  have h3 : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    rw [←Real.sin_two_mul]
    ring_nf
  have h4 : Real.sin β = 2 * Real.sin (β / 2) * Real.cos (β / 2) := by
    rw [←Real.sin_two_mul]
    ring_nf
  have h5 : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
    rw [←Real.cos_two_mul]
    <;> ring_nf
  have h6 : Real.cos β = 2 * Real.cos (β / 2) ^ 2 - 1 := by
    rw [←Real.cos_two_mul]
    <;> ring_nf
  rw [h3, h4, h5, h6]
  have h7 : Real.cos ((Real.pi - α - β) / 2) = Real.sin ((α + β) / 2) := by
    have h8 : (Real.pi - α - β) / 2 = Real.pi / 2 - ( (α + β) / 2 ) := by ring
    rw [h8]
    rw [show Real.pi / 2 - ( (α + β) / 2 ) = Real.pi / 2 - ( (α + β) / 2 ) by ring]
    rw [Real.cos_pi_div_two_sub]
  have h8 : Real.sin ((α + β) / 2) = Real.sin (α / 2) * Real.cos (β / 2) + Real.cos (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring]
    rw [Real.sin_add]
    <;> ring_nf
  rw [h7, h8]
  have h11 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α / 2)
  have h12 : Real.sin (β / 2) ^ 2 + Real.cos (β / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (β / 2)
  -- Simplify trigonometric expressions and collect like terms
  ring_nf
  <;> simp [Real.sin_sq, Real.cos_sq, h11, h12, mul_add, add_mul]
  <;> nlinarith [Real.sin_sq_add_cos_sq (α / 2), Real.sin_sq_add_cos_sq (β / 2), Real.sin_sq_add_cos_sq ((α + β) / 2), Real.sin_sq_add_cos_sq (α + β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq (Real.pi - α - β)]