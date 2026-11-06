import Mathlib

theorem algebra_1178 {n : ℕ} (hn : n ≠ 0) :
    (2 * n + 3 * n + 4 * n = n ^ n) ↔ n = 3 := by 
  constructor
  · -- First direction: if the equation holds, then n = 3
    intro h_eq
    have h1 : n ≥ 1 := by 
      by_contra h
      push_neg at h
      have h0 : n = 0 := by linarith
      contradiction
    have h_eq' : 9 * n = n ^ n := by 
      omega
    have h2 : n ≤ 4 := by
      by_contra h
      push_neg at h
      have h3 : n ^ n > 9 * n := by
        have h3 : n ≥ 4 := by 
          omega
        have base := show 4 ^ 4 > 9 * 4 by norm_num
        have step : ∀ m, m ≥ 4 → (m ^ m > 9 * m) → (m + 1) ^ (m + 1) > 9 * (m + 1) := by
          intro m hm h1
          have h2 : (m + 1) ^ (m + 1) > 9 * (m + 1) := by
            have h4 : (m + 1) ^ (m + 1) > m ^ (m + 1) := by
              apply Nat.pow_lt_pow_left
              all_goals
                omega
            have h5 : m ^ (m + 1) = m * (m ^ m) := by 
              ring_nf
            have h6 : m ^ m > 9 * m := h1
            have h7 : m * (m ^ m) > m * (9 * m) := by
              nlinarith [h6, show m > 0 by omega]
            have h8 : 9 * (m * m) ≥ 9 * (m + 1) := by
              nlinarith [show m≥2 by omega]
            have h9 : m * (m ^ m) > 9 * (m + 1) := by
              nlinarith [h7, h8]
            nlinarith [h4, h5, h9]
          exact h2
        exact Nat.le_induction base step n h3
      linarith
    interval_cases n <;> try { trivial }
    all_goals
      omega
  · -- Second direction: if n = 3, then the equation holds
    intro h_eq
    rw [h_eq]
    all_goals
      norm_num