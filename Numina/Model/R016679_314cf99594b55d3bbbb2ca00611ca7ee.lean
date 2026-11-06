import Mathlib

theorem algebra_317797 (α : ℝ) (h : Real.sin α ^ 3 + Real.cos α ^ 3 > 0) :
    0 < Real.sin α + Real.cos α ∧ Real.sin α + Real.cos α ≤ Real.sqrt 2 := by

  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

  have eq1 : Real.sin α ^ 3 + Real.cos α ^ 3 = 
      (Real.sin α + Real.cos α)^3 - 3 * (Real.sin α * Real.cos α) * (Real.sin α + Real.cos α) := by 
    ring

  have eq2 : Real.sin α * Real.cos α = 
      ((Real.sin α + Real.cos α) ^ 2 - 1) / 2 := by 
    nlinarith [h1, Real.sin_sq_add_cos_sq α]

  have h5 : (Real.sin α + Real.cos α) ^ 2 ≤ 2 := by 
    nlinarith [sq_nonneg (Real.sin α - Real.cos α), Real.sin_sq_add_cos_sq α]

  constructor 
  · -- Prove 0 < Real.sin α + Real.cos α
    by_contra h6 
    push_neg at h6 
    have h7 : Real.sin α + Real.cos α ≤ 0 := by nlinarith 
    have h8 : (Real.sin α + Real.cos α) * (3 - (Real.sin α + Real.cos α) ^ 2) ≤ 0 := by 
      have h9 : Real.sin α + Real.cos α ≤ 0 := by nlinarith 
      have h10 : 3 - (Real.sin α + Real.cos α) ^ 2 ≥ 0 := by 
        nlinarith [sq_nonneg (Real.sin α + Real.cos α), sq_nonneg (Real.sin α - Real.cos α), Real.sin_sq_add_cos_sq α]
      nlinarith 
    have h11 : Real.sin α ^ 3 + Real.cos α ^ 3 = (Real.sin α + Real.cos α) * (3 - (Real.sin α + Real.cos α) ^ 2) := by 
      rw [eq1]
      rw [eq2]
      ring_nf 
      <;> nlinarith 
    nlinarith [h11, h8, h] 
  · -- Prove Real.sin α + Real.cos α ≤ Real.sqrt 2
    have h5a : (Real.sin α + Real.cos α) ^ 2 ≤ 2 := h5 
    have h6b : Real.sqrt 2 ≥ 0 := by positivity 
    have h7b : Real.sin α + Real.cos α ≤ Real.sqrt 2 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sin α + Real.cos α - Real.sqrt 2)]
    linarith