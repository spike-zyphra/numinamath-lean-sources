import Mathlib

theorem algebra_1088 (a b : ℝ) (c : ℝ) (ha : a ≠ b) (h1 : a * c ^ 2 + b * c + 1 = 0) (h2 : b * c ^ 2 + a * c + 1 = 0) :
    1 / (a + b) + c = 0 := by
  have h3 : (a - b) * (c ^ 2 - c) = 0 := by 
    nlinarith
  
  cases (mul_eq_zero.mp h3) with
  | inl h4 =>
    exfalso
    exact ha (by linarith)
    
  | inr h5 =>
    have h6 : c * (c - 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h6) with
    | inl h7 =>
      -- Derive a contradiction if c = 0
      rw [h7] at h1
      nlinarith
    | inr h8 =>
      have hc : c = 1 := by linarith
      have h_sum : a + b = -1 := by 
        rw [hc] at h1
        nlinarith
      rw [h_sum, hc]
      norm_num