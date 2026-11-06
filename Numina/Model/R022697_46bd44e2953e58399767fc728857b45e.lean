import Mathlib

theorem algebra_172212 {x : ℕ} (hx : x ≠ 0) (h : 300 / x - 3 = 300 / (x - 3) + 3) :
    x = 15 := by
  have h1 : x ≤ 303 := by 
    by_contra h2
    push_neg at h2
    have eq1 : 300 / x = 0 := by 
      rw [Nat.div_eq_zero_iff]
      omega 
    have eq2 : 300 / x - 3 = 300 / (x - 3) + 3 := h
    have eq3 : 300 / (x - 3) + 3 = 0 := by 
      rw [eq1] at eq2 
      omega
    have h3 : x - 3 > 300 := by
      omega 
    have eq4 : 300 / (x - 3) = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    have eq5 : (300 / (x - 3) + 3) = (0 : ℕ) := eq3
    rw [eq4] at eq5
    omega
  interval_cases x <;> norm_num at h ⊢