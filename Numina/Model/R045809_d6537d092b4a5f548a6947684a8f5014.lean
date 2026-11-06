import Mathlib

theorem inequalities_45079 (a b c : ℤ) :
    a^2 + b^2 + c^2 + 3 < a * b + 3 * b + 2 * c ↔ (a = 1 ∧ b = 2 ∧ c = 1) := by
  constructor
  · -- Forward direction: if the inequality holds, then (a, b, c) = (1, 2, 1)
    intro h
    have h1 : (a - 1 : ℤ) ^ 2 + (b - 2 : ℤ) ^ 2 + (c - 1 : ℤ) ^ 2 < 4 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 1),
        sq_nonneg (2 * a - b - 2), sq_nonneg (b - 2), sq_nonneg (c - 1)]
    have h2 : (a - 1 : ℤ) ^ 2 ≤ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 1)]
    have h3 : (b - 2 : ℤ) ^ 2 ≤ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 1)]
    have h4 : (c - 1 : ℤ) ^ 2 ≤ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 1)]
    have h5 : a ≤ 4 := by
      nlinarith [sq_nonneg (a - 1)]
    have h6 : a ≥ 0 := by
      nlinarith [sq_nonneg (a - 1)]
    have h7 : b ≤ 5 := by
      nlinarith [sq_nonneg (b - 2)]
    have h8 : b ≥ 0 := by
      nlinarith [sq_nonneg (b - 2)]
    have h9 : c ≤ 4 := by
      nlinarith [sq_nonneg (c - 1)]
    have h10 : c ≥ 0 := by
      nlinarith [sq_nonneg (c - 1)]
    interval_cases a <;> interval_cases b <;> interval_cases c
      <;> omega
  · -- Backward implication: (a, b, c) = (1, 2, 1) implies the inequality
    rintro ⟨rfl, rfl, rfl⟩
    norm_num