import Mathlib

theorem inequalities_191942 (k : ℝ) :
    (∀ a b : ℝ, a^2 + b^2 ≥ k * a * b) ↔ -2 ≤ k ∧ k ≤ 2 := by
  constructor
  · -- Forward direction: assuming the inequality holds for all a, b, prove -2 ≤ k ∧ k ≤ 2
    intro h
    have h1 := h 1 1
    have h2 := h 1 (-1)
    constructor
    · -- Let's prove k ≥ -2
      nlinarith
    · -- Let's prove k ≤ 2
      nlinarith
  · -- Backward direction: assuming -2 ≤ k ≤ 2, prove the inequality holds for all a, b
    rintro ⟨hk1, hk2⟩
    intro a b
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - k * b / 2), sq_nonneg (b - k * a / 2), sq_nonneg (k), sq_nonneg (a * b)]