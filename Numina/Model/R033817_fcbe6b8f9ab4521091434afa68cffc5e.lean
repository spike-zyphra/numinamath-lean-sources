import Mathlib

theorem number_theory_289932 (a b : ℕ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : 2^a * 3^b = 324) : 2^b * 3^a = 144 := by
  have h2 : a ≤ 10 := by
    by_contra h
    push_neg at h
    have h3 : 2^a * 3^b ≥ 2^11 * 3^0 := by
      have h4 : a ≥ 11 := by linarith
      have h5 : 3^b ≥ 3^0 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h6 : 2^a ≥ 2^11 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      nlinarith
    nlinarith
  have h3 : b ≤ 10 := by
    by_contra h
    push_neg at h
    have h4 : 2^a * 3^b ≥ 3^11 * 2^0 := by
      have h5 : b ≥ 11 := by linarith
      have h6 : 3^b ≥ 3^11 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h7 : 2^a ≥ 2^0 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      nlinarith
    nlinarith
  interval_cases a <;> interval_cases b <;> omega