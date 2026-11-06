import Mathlib

theorem algebra_5231 {a b x : ℝ} (h : (a - 4) ^ 2 + (b + 3) ^ 2 = 0) (h' : b * x + 3 * a = -3) :
    x = 5 := by
  have h₁ : (a - 4) ^ 2 = 0 := by 
    have h1_nonneg : (a - 4) ^ 2 ≥ 0 := sq_nonneg (a - 4)
    have h2_nonneg : (b + 3) ^ 2 ≥ 0 := sq_nonneg (b + 3)
    have h_zero : (a - 4) ^ 2 = 0 := by
      linarith
    exact h_zero
  have ha : a - 4 = 0 := by 
    rw [sq_eq_zero_iff] at h₁
    exact h₁
  have ha' : a = 4 := by 
    linarith
  have h₂ : (b + 3) ^ 2 = 0 := by 
    have h1_nonneg : (a - 4) ^ 2 ≥ 0 := sq_nonneg (a - 4)
    have h2_nonneg : (b + 3) ^ 2 ≥ 0 := sq_nonneg (b + 3)
    have h_zero : (b + 3) ^ 2 = 0 := by 
      linarith
    exact h_zero
  have hb : b + 3 = 0 := by 
    rw [sq_eq_zero_iff] at h₂
    exact h₂
  have hb' : b = -3 := by 
    linarith
  rw [hb', ha'] at h'
  linarith