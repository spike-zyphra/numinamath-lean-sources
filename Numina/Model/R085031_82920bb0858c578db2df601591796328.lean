import Mathlib

theorem algebra_2318 {a b : ℤ} (h : |a - 1| + |b + 2| = 1) :
  (a - 1)^2 * (b + 2)^4 = 0 := by 
  have h1 : |a - 1| ≤ 1 := by
    linarith [abs_nonneg (a - 1), abs_nonneg (b + 2)]
  have h2 : |b + 2| ≤ 1 := by
    linarith [abs_nonneg (a - 1), abs_nonneg (b + 2)]
  have h3 : |a - 1| = 0 ∨ |a - 1| = 1 := by 
    omega 
  cases h3 with
  | inl h5 => 
    have ha1 : a - 1 = 0 := by 
      simpa [abs_eq_zero] using h5 
    have h2_eq : |b + 2| = 1 := by 
      linarith [h, h5]
    have h_zero : (a - 1)^2 * (b + 2)^4 = 0 := by
      rw [show a - 1 = 0 by linarith]
      norm_num 
    exact h_zero 
  | inr h6 => 
    have hb1 : |b + 2| = 0 := by 
      linarith [h, h6]
    have hb2 : b + 2 = 0 := by 
      simpa [abs_eq_zero] using hb1 
    have h_zero : (a - 1)^2 * (b + 2)^4 = 0 := by 
      rw [show b + 2 = 0 by linarith]
      norm_num 
    exact h_zero