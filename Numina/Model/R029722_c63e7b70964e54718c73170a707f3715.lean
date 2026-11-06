import Mathlib

theorem algebra_209771 (n : ℕ) :
    (∃ a b : ℤ, n^2 = a + b ∧ n^3 = a^2 + b^2) ↔
    (n = 0 ∨ n = 1 ∨ n = 2) := by
  constructor
  · -- Forward implication: from existence of a, b proving n = 0, 1, 2
    rintro ⟨a, b, h1, h2⟩
    have h3 : (n : ℤ) ^ 2 = a + b := by 
      exact_mod_cast h1
    have h4 : (n : ℤ) ^ 3 = a ^ 2 + b ^ 2 := by 
      exact_mod_cast h2
    -- Derive constraint from n^4 ≤ 2n^3
    have h6 : (n : ℤ) ^ 4 ≤ 2 * ((n : ℤ) ^ 3) := by
      have h10 : (a + b : ℤ) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
        nlinarith [sq_nonneg (a - b)]
      have h11 : (a + b : ℤ) = (n : ℤ) ^ 2 := by
        linarith [h3]
      have h12 : a ^ 2 + b ^ 2 = (n : ℤ) ^ 3 := by 
        linarith [h4]
      rw [h11] at h10
      rw [h12] at h10
      nlinarith
    -- From h6 derived above
    have h6' : (n : ℤ) ^ 3 * ((n : ℤ) - 2) ≤ 0 := by
      nlinarith
    -- From h6' given n is a natural number
    have h7 : n ≤ 2 := by
      by_contra h
      push_neg at h
      have h8 : n ≥ 3 := by
        omega
      have h9 : (n : ℤ) ≥ 3 := by
        exact_mod_cast h8
      nlinarith
    interval_cases n <;> tauto
  · -- Backward implication: from n = 0, 1, 2 proving existence of a, b
    rintro (rfl | rfl | rfl)
    · -- n = 0
      use 0, 0
      all_goals
        norm_num
    · -- n = 1
      use 0, 1
      all_goals
        norm_num
    · -- n = 2
      use 2, 2
      all_goals
        norm_num