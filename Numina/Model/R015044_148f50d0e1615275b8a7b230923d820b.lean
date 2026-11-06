import Mathlib

theorem algebra_191437 {a b c : ℤ} (h : a - b - 4 = (8 + b) * (-3 - b)) (h' : b - (c + 3) = (4 + b) * (-3 - b)) (h'' : c = (c + 3) * (-3 - b)) :
    a = 5 ∧ b = -5 ∧ c = -6 := by
  have eq4 : b = -5 := by
    have eq5 : b ≤ 5 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b + 5), sq_nonneg (c + 6), sq_nonneg (a + b + 5), sq_nonneg (c + b + 6), sq_nonneg (a - b - 2)]
    have eq6 : b ≥ -15 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (b + 5), sq_nonneg (c + 6), sq_nonneg (a + b + 5), sq_nonneg (c + b + 6), sq_nonneg (a - b - 2)]
    interval_cases b <;> omega 
  have eq5 : a = 5 := by 
    rw [show b = -5 by linarith [eq4]] at h
    nlinarith 
  have eq6 : c = -6 := by 
    rw [show b = -5 by linarith [eq4]] at h' h''
    nlinarith [eq5]
  exact ⟨eq5, eq4, eq6⟩