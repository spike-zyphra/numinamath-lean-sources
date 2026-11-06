import Mathlib

theorem number_theory_3450 {n : ℕ} (hn : n^72 < 5^96) (hn' : (n+1)^72 > 5^96) :
    n = 8 := by
  have h1 : n ≤ 8 := by
    by_contra h
    push_neg at h
    have h2 : n ≥ 9 := by
      omega
    have h3 : n ^ 72 ≥ 9 ^ 72 := by
      apply Nat.pow_le_pow_of_le_left
      omega
    have h5 : 9 ^ 72 > 5 ^ 96 := by
      norm_num
    linarith
  have h6 : n ≥ 8 := by
    by_contra h
    push_neg at h
    have h7 : n ≤ 7 := by
      omega
    have h8 : (n + 1) ≤ 8 := by
      omega
    have h9 : (n + 1) ^ 72 ≤ 8 ^ 72 := by
      apply Nat.pow_le_pow_of_le_left
      omega
    have h11 : 8 ^ 72 < 5 ^ 96 := by
      norm_num
    linarith
  have h2 : n = 8 := by 
    omega
  exact h2