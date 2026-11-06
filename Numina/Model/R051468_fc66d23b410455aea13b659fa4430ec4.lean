import Mathlib

theorem algebra_2638 {x y : ℝ} (h : x^2 * y^2 + x^2 + y^2 + 10 * x * y + 16 = 0) :
    (x = 2 ∧ y = -2) ∨ (x = -2 ∧ y = 2) := by

  have h1 : (x * y + 4) ^ 2 + (x + y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x * y + 4), sq_nonneg (x + y),
      sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y)]
  
  have h2 : (x * y + 4) ^ 2 = 0 := by nlinarith [sq_nonneg (x * y + 4), sq_nonneg (x + y)]
  
  have h3 : (x + y) ^ 2 = 0 := by nlinarith [sq_nonneg (x * y + 4), sq_nonneg (x + y)]

  have h4 : x * y + 4 = 0 := by
    rwa [sq_eq_zero_iff] at h2

  have h5 : x + y = 0 := by
    rwa [sq_eq_zero_iff] at h3
  
  have h6 : y = -x := by linarith
  
  rw [h6] at h4
  
  have h7 : x^2 = 4 := by
    nlinarith
  
  have h8 : x = 2 ∨ x = -2 := by
    have h9 : x^2 - 4 = 0 := by
      nlinarith
    
    have h10 : (x - 2) * (x + 2) = 0 := by
      nlinarith
    
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case $x - 2 = 0$, so $x = 2$
      left
      linarith
    · -- Case $x + 2 = 0$, so $x = -2$
      right
      nlinarith
  
  cases h8 with
  | inl h9 =>
    have h10 : y = -2 := by
      rw [h9] at h6
      linarith
    left
    exact ⟨h9, h10⟩
  | inr h9 =>
    have h10 : y = 2 := by
      rw [show x = -2 by linarith ] at h6
      linarith
    right
    exact ⟨by linarith, h10⟩