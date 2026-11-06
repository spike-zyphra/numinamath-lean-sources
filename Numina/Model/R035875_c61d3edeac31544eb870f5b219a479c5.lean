import Mathlib

theorem algebra_168602 (α β : ℝ) (h1 : 3 * (Real.sin α) ^ 2 + 2 * (Real.sin β) ^ 2 = 1)
    (h2 : 3 * (Real.sin α + Real.cos α) ^ 2 - 2 * (Real.sin β + Real.cos β) ^ 2 = 1) :
    Real.cos (2 * (α + β)) = -1 / 3 := by
  have eq1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have eq2 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have eq5 : 3 * (Real.sin α ^ 2 + Real.cos α ^ 2 + 2 * Real.sin α * Real.cos α) - 2 * (Real.sin β ^ 2 + Real.cos β ^ 2 + 2 * Real.sin β * Real.cos β) = 1 := by
    nlinarith [h2, eq1, eq2, sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β), sq_nonneg (Real.sin α + Real.cos α - (Real.sin β + Real.cos β))]
  have eq7 : 6 * Real.sin α * Real.cos α = 4 * Real.sin β * Real.cos β := by 
    nlinarith [eq5, eq1, eq2]

  have h5 : Real.cos (2 * (α + β)) = Real.cos (2 * α) * Real.cos (2 * β) - Real.sin (2 * α) * Real.sin (2 * β) := by 
    have h1 : 2 * (α + β) = 2 * α + 2 * β := by ring 
    rw [h1]
    rw [Real.cos_add]

  have eq3 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
    have h1 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
      rw [Real.cos_two_mul]
      rw [Real.sin_sq]
      ring 
    exact h1

  have eq4 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
    have h1 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
      rw [Real.sin_two_mul]
    exact h1

  have eq5 : Real.cos (2 * β) = 1 - 2 * Real.sin β ^ 2 := by
    have h1 : Real.cos (2 * β) = 1 - 2 * Real.sin β ^ 2 := by 
      rw [Real.cos_two_mul]
      rw [Real.sin_sq]
      ring 
    exact h1

  have eq6 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by
    have h1 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by
      rw [Real.sin_two_mul]
    exact h1

  rw [h5, eq3, eq5, eq4, eq6]
  nlinarith [sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β), sq_nonneg (Real.sin α * Real.cos α - Real.sin β * Real.cos β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α ^ 2 - Real.sin β ^ 2), sq_nonneg (Real.cos α ^ 2 - Real.cos β ^ 2)]