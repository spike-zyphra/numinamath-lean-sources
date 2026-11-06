import Mathlib


theorem number_theory_38941 : {(p, m) : ℕ×ℕ | 0 < p ∧ 0 < m ∧ Nat.Prime p ∧ p * (p + m) + p = (m + 1) ^ 3} = {(2, 1)} := by
  ext ⟨p, m⟩
  simp
  constructor
  · rintro ⟨hp, hm, h2, heq⟩
    have eq1 : p ≥ 2 := Nat.Prime.two_le h2
    have eq2 : m = 1 := by
      by_cases h : m > 1
      · -- m > 1, so m ≥ 2
        have h3 : m ≥ 2 := by omega
        have eq3 : p * (p + m + 1) = (m + 1) ^ 3 := by linarith
        have eq4 : p ∣ (m + 1) ^ 3 := by
          have eq2' : p ∣ p * (p + m + 1) := by
            use (p + m + 1)
            all_goals
              ring
          rw [eq3] at eq2'
          exact eq2'
        have eq5 : p ∣ (m + 1) := by
          have h6 : p ∣ (m + 1) ^ 3 := eq4
          have h7 : p ∣ (m + 1) := by
            apply Nat.Prime.dvd_of_dvd_pow h2
            exact h6
          exact h7
        rcases eq5 with ⟨k, hk⟩
        have eq7 : m + 1 = p * k := by
          linarith
        have eq8 : p * (p + m + 1) = (m + 1) ^ 3 := by
          linarith
        rw [show m + 1 = p * k by linarith] at eq8
        have eq10 : p * (p + m + 1) = (p * k) ^ 3 := by
          linarith
        have eq11 : p * (p + m + 1) = p^3 * k^3 := by
          ring_nf at eq10 ⊢
          linarith
        have eq12 : p + m + 1 = p^2 * k^3 := by
          have h13 : p ≥ 2 := eq1
          have h1 : p > 0 := by linarith
          have : p + m + 1 = p^2 * k^3 := by
            nlinarith
          exact this
        have eq13 : k + 1 = p * k^3 := by
          have eq9' : m + 1 = p * k := eq7
          have eq10' : p + m + 1 = p + (m + 1) := by ring
          rw [eq10'] at eq12
          rw [eq9'] at eq12
          have h17 : p + p * k = p * (k + 1) := by
            ring
          nlinarith
        have eq14 : k = 1 := by
          by_cases hk1 : k > 1
          · -- k > 1, so k ≥ 2
            have hk11 : k ≥ 2 := by omega
            have h6 : p ≥ 2 := eq1
            have h7 : k + 1 = p * k^3 := eq13
            nlinarith [sq_nonneg (k : ℕ), sq_nonneg (p : ℕ), sq_pos_of_pos (show 0 < (k : ℕ) by omega)]
          have eq14 : k ≤ 1 := by omega
          interval_cases k <;> try omega
        have eq15 : p = 2 := by
          rw [eq14] at eq13
          nlinarith
        have eq16 : m = 1 := by
          rw [eq15] at hk
          nlinarith
        omega
      · -- m ≤ 1, so since m ≥ 1, m = 1
        omega
    have eq3 : p = 2 := by
      rw [eq2] at heq
      have eq5 : p * (p + 1) + p = (1 + 1) ^ 3 := by
        linarith
      have eq5' : p ≤ 3 := by
        have h6 : p^2 ≤ 8 := by
          nlinarith
        have h7 : p ≤ 3 := by nlinarith
        exact h7
      interval_cases p <;> norm_num at eq5 h2 ⊢ <;> try tauto
    simp [eq3, eq2]
  · -- When (p, m) = (2, 1)
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num