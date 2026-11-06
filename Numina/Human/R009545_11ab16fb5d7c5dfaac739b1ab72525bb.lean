import Mathlib

theorem algebra_169456 :
    ∃ a b : ℝ, ∀ p q : ℝ, -(p / 2) ^ 2 + p * (p / 2) + q = (p / 2) ^ 2 → b = -a ^ 2 + p * a + q ∧ b = a ^ 2 := by
  -- The common point required is (0, 0).
  use 0, 0
  intro p q h
  simp
  -- It suffices to show that q = 0, which is obvious from p ^ 2 / 4 + q = (p / 2) ^ 2.
  linarith