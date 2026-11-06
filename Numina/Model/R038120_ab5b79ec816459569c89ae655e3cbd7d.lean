import Mathlib

theorem algebra_3725 {a b : ℤ} (h : (a-2)^2+(b+17)^2=0) : a=2 ∧ b=-17 := by
  have h1 : (a - 2) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h2 : (b + 17) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h3 : (a - 2) ^ 2 = 0 := by 
    linarith
  have h4 : (b + 17) ^ 2 = 0 := by 
    linarith
  have h5 : a - 2 = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have ha : a = 2 := by
    linarith
  have h6 : b + 17 = 0 := by
    rwa [sq_eq_zero_iff] at h4
  have hb : b = -17 := by 
    linarith
  exact ⟨ha, hb⟩