import Mathlib

theorem algebra_303229 (a : ℕ) (ha : 0 ≤ a) (h : ∃ x : ℤ, a^2 * x^2 - (3 * a^2 - 8 * a) * x + 2 * a^2 - 13 * a + 15 = 0) :
    a = 1 ∨ a = 3 ∨ a = 5 := by
  rcases h with ⟨x, hx⟩
  have h1 : (a : ℤ) ^ 2 * x ^ 2 - (3 * (a : ℤ) ^ 2 - 8 * (a : ℤ)) * x + 2 * (a : ℤ) ^ 2 - 13 * (a : ℤ) + 15 = 0 := by
    exact_mod_cast hx
  have h2 : ((a : ℤ) * x - (a - 5)) * ((a : ℤ) * x - (2 * (a) - 3)) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case 1: (a * x - (a - 5)) = 0
    have h5 : (a : ℤ) * x = (a - 5 : ℤ) := by
      linarith
    have h6 : (a : ℤ) * (x - 1) = -5 := by
      nlinarith
    have h7 : (a : ℤ) ∣ -5 := by
      use (x - 1)
      all_goals linarith
    have h8 : (a : ℤ) ∣ (5 : ℤ) := by
      exact Int.dvd_neg.mp h7
    have h9 : a ∣ 5 := by
      have h2 : (a : ℤ) ∣ (5 : ℤ) := h8
      norm_cast at h2 ⊢
    have h10 : a = 1 ∨ a = 5 := by
      have h11 : a ∣ 5 := h9
      have h12 : a ≤ 5 := by
        exact Nat.le_of_dvd (by norm_num) h11
      interval_cases a <;> tauto
    rcases h10 with (h11 | h11)
    · -- Case 1a: a = 1
      left
      tauto
    · -- Case 1b: a = 5
      right
      right
      tauto
  · -- Case 2: (a * x - (2 * a - 3)) = 0
    have h7 : (a : ℤ) * x = (2 * (a) - 3 : ℤ) := by
      linarith
    have h8 : (a : ℤ) * (x - 2) = -3 := by
      nlinarith
    have h9 : (a : ℤ) ∣ -3 := by
      use (x - 2)
      all_goals linarith
    have h10 : (a : ℤ) ∣ (3 : ℤ) := by
      exact Int.dvd_neg.mp h9
    have h11 : a ∣ 3 := by
      have h2 : (a : ℤ) ∣ (3 : ℤ) := h10
      norm_cast at h2 ⊢
    have h12 : a = 1 ∨ a = 3 := by
      have h13 : a ∣ 3 := h11
      have h14 : a ≤ 3 := by
        exact Nat.le_of_dvd (by norm_num) h13
      interval_cases a <;> tauto
    rcases h12 with (h13 | h13)
    · -- Case 2a: a = 1
      left
      tauto
    · -- Case 2b: a = 3
      right
      left
      tauto