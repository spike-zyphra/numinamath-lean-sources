import Mathlib

theorem number_theory_158280 (n : ℕ) :
    n + (Nat.digits 10 n).sum = 2021 ↔ n = 2014 ∨ n = 1996 := by
  constructor
  · -- Forward: if n + sum of digits equals 2021, then n = 2014 or 1996
    intro h
    have h1 : n ≤ 2021 := by 
      by_contra h2
      push_neg at h2
      have h3 : (Nat.digits 10 n).sum ≥ 0 := by 
        apply Nat.zero_le
      omega

    have h2 : n ≥ 1985 := by
      by_contra h3
      push_neg at h3
      interval_cases n <;> norm_num at h <;> all_goals omega

    interval_cases n <;> norm_num at h
    <;> tauto
  · -- Backward: if n = 2014 or 1996, then n + sum of digits equals 2021
    rintro (h | h)
    · -- Case n = 2014
      rw [h]
      norm_num
    · -- Case n = 1996
      rw [h]
      norm_num