import Mathlib

theorem number_theory_13621 (a : ℕ) (ha : a^6 ≤ 7^13) :
    a ≤ 67 := by 
  by_contra h
  push_neg at h
  have h1 : a ≥ 68 := by 
    omega
  have h2 : a^6 ≥ 68^6 := by 
    apply Nat.pow_le_pow_of_le_left 
    linarith 
    all_goals omega
  have h3 : a^6 > 7^13 := by
    norm_num at h2 ⊢ 
    linarith
  linarith