import Mathlib

theorem algebra_195207 (c : ℕ) (h : ∑ i ∈ Finset.range 9, 3^i = (3^c - 1) / 2) :
    c = 9 := by
  -- Calculate the sum
  norm_num [Finset.sum_range_succ] at h
  have h1 : c ≤ 9 := by
    by_contra h1
    push_neg at h1
    have h2 : (3 : ℕ) ^ c ≥ (3 : ℕ) ^ 10 := by
      have h3 : c ≥ 10 := by omega
      have h4 : (3 : ℕ) ^ c ≥ (3 : ℕ) ^ 10 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h3
      omega
    have h5 : (3 ^ c - 1) / 2 ≥ (3 ^ 10 - 1) / 2 := by
      omega
    omega
  have h2 : c ≥ 9 := by
    by_contra h2
    push_neg at h2
    have h3 : c ≤ 8 := by omega
    interval_cases c <;> omega
  have h3 : c = 9 := by 
    omega
  exact h3