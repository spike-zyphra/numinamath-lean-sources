import Mathlib

theorem algebra_284086 (α β : ℝ) (h₁ : Real.sin α + Real.sin β = Real.sqrt 6 / 3)
    (h₂ : Real.cos α + Real.cos β = Real.sqrt 3 / 3) :
    Real.cos ((α - β) / 2) ^ 2 = 1 / 4 := by

  have h3 : (Real.sin α + Real.sin β)^2 + (Real.cos α + Real.cos β)^2 = 4 * Real.cos ((α - β) / 2) ^ 2 := by
    have h4 : Real.sin α + Real.sin β = 2 * Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2) := by
      have h5 : Real.sin α = Real.sin ((α + β) / 2 + (α - β) / 2) := by ring_nf
      have h6 : Real.sin β = Real.sin ((α + β) / 2 - (α - β) / 2) := by ring_nf
      rw [h5, h6]
      rw [Real.sin_add, Real.sin_sub]
      ring_nf
      <;> simp [Real.sin_sq, Real.cos_sq]
      <;> ring_nf
    have h7 : Real.cos α + Real.cos β = 2 * Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2) := by
      have h8 : Real.cos α = Real.cos ((α + β) / 2 + (α - β) / 2) := by ring_nf
      have h9 : Real.cos β = Real.cos ((α + β) / 2 - (α - β) / 2) := by ring_nf
      rw [h8, h9]
      rw [Real.cos_add, Real.cos_sub]
      ring_nf
      <;> simp [Real.sin_sq, Real.cos_sq]
      <;> ring_nf
    rw [h4, h7]
    have h11 : Real.sin ((α + β) / 2)^2 + Real.cos ((α + β) / 2)^2 = 1 := Real.sin_sq_add_cos_sq ((α + β) / 2)
    have h10 : (2 * Real.sin ((α + β) / 2) * Real.cos ((α - β) / 2))^2 + (2 * Real.cos ((α + β) / 2) * Real.cos ((α - β) / 2))^2 =
            4 * Real.cos ((α - β) / 2)^2 * (Real.sin ((α + β) / 2)^2 + Real.cos ((α + β) / 2)^2) := by 
      ring_nf
      <;> simp [Real.sin_sq, Real.cos_sq]
      <;> ring_nf
    rw [h10, h11]
    ring_nf

  rw [h₁, h₂] at h3

  have h6 : (Real.sqrt 6 / 3)^2 + (Real.sqrt 3 / 3)^2 = 1 := by
    have h7 : (Real.sqrt 6 / 3 : ℝ)^2 = (6 : ℝ) / 9 := by
      calc
        (Real.sqrt 6 / 3 : ℝ)^2 = (Real.sqrt 6)^2 / 9 := by ring_nf
        _ = 6 / 9 := by rw [Real.sq_sqrt]; all_goals norm_num
    have h8 : (Real.sqrt 3 / 3 : ℝ)^2 = (3 : ℝ) / 9 := by
      calc
        (Real.sqrt 3 / 3 : ℝ)^2 = (Real.sqrt 3)^2 / 9 := by ring_nf
        _ = 3 / 9 := by rw [Real.sq_sqrt]; all_goals norm_num
    rw [h7, h8]
    norm_num
  have h12 : 4 * Real.cos ((α - β) / 2)^2 = 1 := by
    linarith [h3, h6]
  have h13 : Real.cos ((α - β) / 2)^2 = 1 / 4 := by
    linarith
  exact h13