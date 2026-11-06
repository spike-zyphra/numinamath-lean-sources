import Mathlib

theorem algebra_239484 {x y : ℕ} (h1 : 2^x * 3^y = 24) (h2 : 2^y * 3^x = 54) :
    x = 3 ∧ y = 1 := by 
  have h3 : x ≤ 5 := by
    by_contra h
    push_neg at h
    have h4 : 2^x ≥ 2^6 := by
      have h5 : x ≥ 6 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) h5
    have h5 : 3^y ≥ 3^0 := by
      have h6 : y ≥ 0 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) h6
    have h7 : 2^x * 3^y ≥ 2^6 * 3^0 := by
      exact mul_le_mul h4 h5 (by positivity) (by positivity)
    norm_num at h7 h1
    all_goals linarith
  have h4 : y ≤ 5 := by
    by_contra h
    push_neg at h
    have h8 : 3^y ≥ 3^6 := by
      have h9 : y ≥ 6 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) h9
    have h9 : 2^x ≥ 2^0 := by
      have h10 : x ≥ 0 := by omega
      exact Nat.pow_le_pow_of_le_right (by norm_num) h10
    have h10 : 2^x * 3^y ≥ 2^0 * 3^6 := by
      exact mul_le_mul h9 h8 (by positivity) (by positivity)
    norm_num at h10 h1
    all_goals linarith
  interval_cases x <;> interval_cases y <;> omega