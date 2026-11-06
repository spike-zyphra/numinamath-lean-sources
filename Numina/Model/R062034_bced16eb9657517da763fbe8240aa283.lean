import Mathlib

theorem number_theory_152315 : IsGreatest {n | 0 ≤ n ∧ (2 ^ n : ℤ) ∣ (7 ^ 2048 - 1)} 14 := by 
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro n hn
    rcases hn with ⟨hn0, h⟩
    -- We need to show that $n \leq 14$
    have h2 : n ≤ 14 := by
      by_contra h3
      push_neg at h3
      -- If h3 holds and n > 14, then $2^{15}$ divides $7^{2048}-1$, which is false
      have h4 : (2 ^ n : ℤ) ∣ (7 ^ 2048 - 1) := h
      have h5 : n ≥ 15 := by omega
      have h6 : (2 ^ 15 : ℤ) ∣ (2 ^ n : ℤ) := by 
        have h7 : (2 ^ 15 : ℤ) ∣ (2 ^ n : ℤ) := by
          exact pow_dvd_pow _ h5
        exact h7
      have h7 : (2 ^ 15 : ℤ) ∣ (7 ^ 2048 - 1) := by 
        have h8 : (2 ^ 15 : ℤ) ∣ (2 ^ n : ℤ) := by 
          have h9 : (2 ^ 15 : ℤ) ∣ (2 ^ n : ℤ) := by
            exact pow_dvd_pow _ (by omega)
          exact h9
        have h9 : (2 ^ n : ℤ) ∣ (7 ^ 2048 - 1) := h
        exact dvd_trans h8 h9
      -- The Lean tactic norm_num can compute that $2^{15}$ does not divide $7^{2048}-1$, which leads to a contradiction
      norm_num at h7
    linarith