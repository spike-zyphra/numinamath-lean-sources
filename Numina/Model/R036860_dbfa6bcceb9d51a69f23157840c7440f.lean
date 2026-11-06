import Mathlib

theorem algebra_266008 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b + 2 = a^3 + 2 * b) :
    (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 25) ∨ (a = 4 ∧ b = 31) ∨
    (a = 5 ∧ b = 41) ∨ (a = 8 ∧ b = 85) := by
  have h1 : a ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h2' : a > 8 := by linarith
    have h3 : b ≤ a^2 + 2 * a + 4 := by
      by_contra h4
      push_neg at h4
      have h4 : b > a^2 + 2 * a + 4 := by nlinarith
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), sq_nonneg ((a : ℕ) - 1 : ℤ), sq_nonneg ((b : ℕ) - 1 : ℤ), mul_pos ha hb]
    nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), sq_nonneg ((a : ℕ) - 1 : ℤ), sq_nonneg ((b : ℕ) - 1 : ℤ), mul_pos ha hb]
  interval_cases a <;> try { 
    omega
  }
  all_goals omega