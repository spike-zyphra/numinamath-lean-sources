import Mathlib

theorem inequalities_100129 : IsGreatest {n | n ^ 6033 < 2011 ^ 2011} 12 := by
  constructor
  · -- First, we verify 12 is in the set
    show (12 : ℕ) ^ 6033 < 2011 ^ 2011
    norm_num
  · -- Then, we prove it is the greatest
    intro n hn
    have h : n ^ 6033 < 2011 ^ 2011 := hn
    -- Assume for contradiction n > 12, so n >= 13
    by_contra h'
    push_neg at h'
    have h1 : n ≥ 13 := by omega
    -- Then n^6033 >= 13^6033
    have h2 : n ^ 6033 ≥ 13 ^ 6033 := by
      apply Nat.pow_le_pow_of_le_left
      linarith
    -- But 13^6033 > 2011^2011
    have h3 : 13 ^ 6033 > 2011 ^ 2011 := by
      norm_num
    linarith