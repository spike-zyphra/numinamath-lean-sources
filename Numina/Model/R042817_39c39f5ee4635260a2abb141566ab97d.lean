import Mathlib
theorem number_theory_608715 (a b : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) : (∃ k : ℕ, a * 10 ^ 3 + a * 10 ^ 2 + b * 10 ^ 1 + b * 10 ^ 0 = k ^ 2) ↔ (a = 7 ∧ b = 4):= by
  constructor
  · -- Assume that there exists a natural number k such that a * 10 ^ 3 + a * 10 ^ 2 + b * 10 ^ 1 + b * 10 ^ 0 = k ^ 2, prove that a = 7 ∧ b = 4
    rintro ⟨k, hk⟩
    have h1 : a ≤ 9 := by
      omega
    have h2 : b ≤ 9 := by 
      omega
    have h3 : a * 10 ^ 3 + a * 10 ^ 2 + b * 10 ^ 1 + b * 10 ^ 0 = 1100 * a + 11 * b := by
      ring
    rw [h3] at hk
    have h4 : k ^ 2 = 11 * (100 * a + b) := by
      nlinarith
    have h5 : k ≤ 99 := by
      nlinarith [show a ≤ 9 by omega, show b ≤ 9 by omega]
    interval_cases k <;> norm_num at h4 hk <;> omega 
  · -- Assume a = 7 ∧ b = 4 prove that there exists k such that a * 10 ^ 3 + a * 10 ^ 2 + b * 10 ^ 1 + b * 10 ^ 0 = k ^ 2
    rintro ⟨rfl, rfl⟩
    use 88
    all_goals norm_num