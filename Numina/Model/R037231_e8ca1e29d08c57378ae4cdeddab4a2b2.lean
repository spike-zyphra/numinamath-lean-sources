import Mathlib

theorem number_theory_608420 :
    IsGreatest {x : ℕ | x ^ 2 ∣ 24 * 35 * 46 * 57} 12 := by
  constructor
  · -- Show 12 is in the set
    show 12 ^ 2 ∣ 24 * 35 * 46 * 57
    norm_num
  · -- Show 12 is greatest element in the set
    intro x hx
    have h : x ^ 2 ∣ 24 * 35 * 46 * 57 := hx
    by_contra h1
    push_neg at h1
    -- We have x > 12, need to show contradiction
    have h2 : x ≤ 1500 := by
      by_contra h3
      push_neg at h3
      have h4 : x ^ 2 > 24 * 35 * 46 * 57 := by
        have h5 : x ≥ 1501 := by
          omega
        have h6 : x ^ 2 ≥ 1501 ^ 2 := by
          have : x ≥ 1501 := h5
          have h7 : x ^ 2 ≥ (1501: ℕ) ^ 2 := by
            apply Nat.pow_le_pow_left
            all_goals omega
          linarith
        nlinarith
      have h5 : x ^ 2 ≤ 24 * 35 * 46 * 57 := by
        exact Nat.le_of_dvd (by positivity) h
      linarith
    interval_cases x <;> norm_num at h ⊢