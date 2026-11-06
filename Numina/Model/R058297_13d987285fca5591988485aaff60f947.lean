import Mathlib

theorem algebra_10865 (α β : ℝ) (h₀ : Real.sin α + Real.sin β = Real.sqrt 6 / 3)
    (h₁ : Real.cos α + Real.cos β = Real.sqrt 3 / 3) :
    (Real.cos ((α - β) / 2))^2 = 1 / 4 := by 
  have h2 : (Real.sin α + Real.sin β)^2 = (Real.sqrt 6 / 3)^2 := by
    rw [h₀]
  have h3 : (Real.cos α + Real.cos β)^2 = (Real.sqrt 3 / 3)^2 := by 
    rw [h₁]
  have h4 : (Real.sqrt 6 / 3) ^ 2 = 2 / 3 := by 
    have h5 : Real.sqrt 6 ^ 2 = 6 := by 
      exact Real.sq_sqrt (by norm_num)
    field_simp
    linarith
  have h6 : (Real.sqrt 3 / 3) ^ 2 = 1 / 3 := by 
    have h7 : Real.sqrt 3 ^ 2 = 3 := by 
      exact Real.sq_sqrt (by norm_num)
    field_simp
    linarith
  rw [h4] at h2 
  rw [h6] at h3 
  have eq1 : Real.sin α ^ 2 + Real.sin β ^ 2 + 2 * (Real.sin α * Real.sin β) = 2 / 3 := by
    nlinarith [h2]
  have eq2 : Real.cos α ^ 2 + Real.cos β ^ 2 + 2 * (Real.cos α * Real.cos β) = 1 / 3 := by
    nlinarith [h3]
  have h10 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h11 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  have eq3 : Real.sin α ^ 2 + Real.sin β ^ 2 + Real.cos α ^ 2 + Real.cos β ^ 2 + 2 * (Real.sin α * Real.sin β + Real.cos α * Real.cos β) = 1 := by
    nlinarith [eq1, eq2, h10, h11]
  have h12 : Real.sin α * Real.sin β + Real.cos α * Real.cos β = -1 / 2 := by 
    nlinarith [eq3]
  have h13 : Real.cos (α - β) = -1 / 2 := by 
    rw [Real.cos_sub]
    nlinarith [h12]
  have h14 : (Real.cos ((α - β) / 2))^2 = (1 + Real.cos (α - β)) / 2 := by 
    have h2 : Real.cos (α - β) = 2 * (Real.cos ((α - β) / 2)) ^ 2 - 1 := by 
      have h3 : Real.cos (α - β) = 2 * (Real.cos ((α - β) / 2)) ^ 2 - 1 := by 
        have h4 : Real.cos (α - β) = 2 * (Real.cos ((α - β) / 2)) ^ 2 - 1 := by 
          rw [← Real.cos_two_mul ((α - β) / 2)]
          ring_nf <;> try tauto 
        linarith [h4]
      linarith [h3]
    nlinarith [h2]
  rw [h13] at h14
  nlinarith