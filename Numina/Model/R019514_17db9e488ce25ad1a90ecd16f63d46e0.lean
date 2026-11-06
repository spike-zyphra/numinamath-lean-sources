import Mathlib

theorem inequalities_43705 (x : ℤ) (h : x > 0) (h1 : 1 / x + 1 / (x + 1) + 1 / (x + 2) > 1 / 45) :
    x + (x + 1) + (x + 2) ≤ 402 := by
  by_contra h2
  push_neg at h2
  have h2' : x > 133 := by 
    omega
  have h3 : x > 1 := by
    omega
  have h4 : 1 / x = 0 := by 
    rw [Int.ediv_eq_zero_of_lt]
    all_goals omega
  have h5 : 1 / (x + 1) = 0 := by 
    rw [Int.ediv_eq_zero_of_lt]
    all_goals omega
  have h6 : 1 / (x + 2) = 0 := by 
    rw [Int.ediv_eq_zero_of_lt]
    all_goals omega
  simp [h4, h5, h6] at h1 
  all_goals omega