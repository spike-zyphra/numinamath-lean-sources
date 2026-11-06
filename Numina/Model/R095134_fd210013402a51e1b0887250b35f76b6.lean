import Mathlib

theorem algebra_153436 (x : ℕ) (hx : 5^x = 625) : x = 4 := by
  have h1 : x ≤ 4 := by
    by_contra h
    push_neg at h
    have h2 : x ≥ 5 := by omega
    have h3 : 5 ^ x ≥ 5 ^ 5 := by 
      apply Nat.pow_le_pow_of_le_right 
      all_goals omega
    have h4 : 5 ^ 5 > 625 := by norm_num
    have h5 : 5 ^ x > 625 := by linarith
    linarith
  interval_cases x <;> norm_num at hx <;> all_goals omega