import Mathlib

theorem algebra_165057 (α β : ℝ) (h₀ : Real.sin (α + β) = 0.2) (h₁ : Real.cos (α - β) = 0.3) :
    Real.sin (α + Real.pi / 4) * Real.sin (β + Real.pi / 4) = 0.25 := by
  have h2 : Real.sin (α + Real.pi / 4) = (Real.sin α + Real.cos α) * (Real.sqrt 2 / 2) := by
    rw [Real.sin_add]
    have hsin : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [hsin, hcos]
    ring
  have h3 : Real.sin (β + Real.pi / 4) = (Real.sin β + Real.cos β) * (Real.sqrt 2 / 2) := by
    rw [Real.sin_add]
    have hsin : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [hsin, hcos]
    ring
  rw [h2, h3]
  have h4 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    rw [Real.sin_add]
  have h5 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
    rw [Real.cos_sub]
  have h6 : (Real.sin α + Real.cos α) * (Real.sin β + Real.cos β) = Real.cos (α - β) + Real.sin (α + β) := by
    rw [h4, h5]
    ring
  have h7 : (Real.sin α + Real.cos α) * (Real.sin β + Real.cos β) = 0.3 + 0.2 := by
    rw [h6, h₀, h₁]
  have h8 : (Real.sin α + Real.cos α) * (Real.sin β + Real.cos β) = 0.5 := by
    rw [h7]
    norm_num
  have h9 : (Real.sqrt 2 / 2) ^ 2 = 0.5 := by
    have h21 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    field_simp
    <;> nlinarith
  calc
    ((Real.sin α + Real.cos α) * (Real.sqrt 2 / 2)) * ((Real.sin β + Real.cos β) * (Real.sqrt 2 / 2))
        = ((Real.sin α + Real.cos α) * (Real.sin β + Real.cos β)) * ((Real.sqrt 2 / 2) ^ 2) := by
          ring
    _ = (0.5) * ((Real.sqrt 2 / 2) ^ 2) := by
      rw [h8]
    _ = (0.5) * (0.5) := by
      rw [h9]
    _ = (0.25 : ℝ) := by
      norm_num