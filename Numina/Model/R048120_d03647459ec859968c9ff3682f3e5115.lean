import Mathlib

theorem algebra_312688 (α β : ℝ) :
    1 - 1 / 4 * (Real.sin (2 * α))^2 - (Real.sin β)^2 - (Real.cos α)^4 =
    Real.sin (α + β) * Real.sin (α - β) := by
  -- First, use the double-angle formula for sin(2α) = 2 sin α cos α
  have h1 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]

  -- Compute sin^2(2α) = (2 sin α cos α) ^2 = 4 sin^2 α cos^2 α
  have h2 : (Real.sin (2 * α)) ^ 2 = 4 * (Real.sin α) ^ 2 * (Real.cos α) ^ 2 := by 
    rw [h1]
    ring

  -- Now show that the left side simplifies to sin^2 α - sin^2 β
  have h3 : 1 - 1 / 4 * (Real.sin (2 * α)) ^ 2 - (Real.sin β) ^ 2 - (Real.cos α) ^ 4 =
    (Real.sin α) ^ 2 - (Real.sin β) ^ 2 := by
    rw [h2]
    have h4 : (Real.sin α) ^ 2 + (Real.cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α - Real.cos α), sq_nonneg (Real.sin β - Real.cos β)]
  
  have h4 : Real.sin (α + β) * Real.sin (α - β) = (Real.sin α) ^ 2 - (Real.sin β) ^ 2 := by
    have eq1 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by 
      rw [Real.sin_add]
    have eq2 : Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β := by
      rw [Real.sin_sub]
    rw [eq1, eq2]
    have eq3 : (Real.sin α * Real.cos β + Real.cos α * Real.sin β) * (Real.sin α * Real.cos β - Real.cos α * Real.sin β) = (Real.sin α * Real.cos β) ^ 2 - (Real.cos α * Real.sin β) ^ 2 := by
      ring
    have eq4 : (Real.sin α * Real.cos β) ^ 2 - (Real.cos α * Real.sin β) ^ 2 = (Real.sin α) ^ 2 - (Real.sin β) ^ 2 := by 
      have h5' : (Real.cos α) ^ 2 = 1 - (Real.sin α) ^ 2 := by 
        have h : (Real.sin α) ^ 2 + (Real.cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α
        linarith
      have h6' : (Real.cos β) ^ 2 = 1 - (Real.sin β) ^ 2 := by 
        have h : (Real.sin β) ^ 2 + (Real.cos β) ^ 2 = 1 := Real.sin_sq_add_cos_sq β
        linarith
      have eq5 : (Real.sin α * Real.cos β) ^ 2 = (Real.sin α) ^ 2 * (Real.cos β) ^ 2 := by ring
      have eq6 : (Real.cos α * Real.sin β) ^ 2 = (Real.cos α) ^ 2 * (Real.sin β) ^ 2 := by ring
      rw [eq5, eq6, h5', h6']
      <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
    linarith [eq3, eq4]

  rw [h3]
  linarith [h4]