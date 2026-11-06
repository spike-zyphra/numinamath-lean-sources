import Mathlib

theorem algebra_292351 {a b c : ℝ} :
    (2 * (a + 1) * (b + 1) = (a + b) * (a + b + 2) → a ^ 2 + b ^ 2 = 2) ∧
    (a ^ 2 + c ^ 2 = 2 * b ^ 2 → (a + b) * (a + c) + (c + a) * (c + b) = 2 * (b + a) * (b + c)) := by
  constructor
  · -- Proof of the first implication
    intro h
    nlinarith [h]
  · -- Proof of the second implication
    intro h
    nlinarith [h]