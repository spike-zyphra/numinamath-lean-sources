import Mathlib

theorem algebra_213084 {x : ℝ} (hx : x^2 - 1 ≥ 0) :
    (x^2 + x)^2 + Real.sqrt (x^2 - 1) = 0 ↔ x = -1 := by
  constructor
  · -- Forward direction: If the equation holds, then x = -1
    intro h
    have h1 : (x^2 + x)^2 ≥ 0 := by
      apply sq_nonneg
    have h2 : Real.sqrt (x^2 - 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : (x^2 + x)^2 = 0 := by
      linarith [h1, h2, h]
    have h4 : Real.sqrt (x^2 - 1) = 0 := by
      linarith [h1, h2, h]
    have h5 : x^2 + x = 0 := by 
      rw [sq_eq_zero_iff] at h3
      exact h3
    have h6 : x^2 - 1 = 0 := by 
      rw [Real.sqrt_eq_zero (by linarith)] at h4
      linarith
    have h7 : x^2 = 1 := by 
      linarith
    have h8 : x = 1 ∨ x = -1 := by
      rw [sq_eq_one_iff] at h7
      exact h7
    cases h8 with
    | inl h9 =>
      rw [h9] at h5
      norm_num at h5
    | inr h10 =>
      exact h10
  · -- Reverse direction: If x = -1, then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt ((-1 : ℝ)^2 - 1) = 0 := by
      rw [Real.sqrt_eq_zero (by norm_num)]
      norm_num
    rw [h1]
    norm_num