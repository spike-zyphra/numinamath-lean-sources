import Mathlib

theorem algebra_317987 (a b : ℝ) (ha : a < b) (f : ℝ → ℝ) (hf : ∀ x, f x = abs (x - a) - abs (x - b)) :
    ∀ x, a - b ≤ f x ∧ f x ≤ b - a := by
  intro x
  have h1 : f x = abs (x - a) - abs (x - b) := hf x
  rw [h1]
  by_cases h2 : x ≥ b
  · -- case x ≥ b
    rw [abs_of_nonneg (show x - a ≥ 0 by linarith), abs_of_nonneg (show x - b ≥ 0 by linarith)]
    constructor
    · -- prove a-b ≤ (x - a) - (x - b)
      nlinarith
    · -- prove (x - a) - (x - b) ≤ b - a
      nlinarith
  · -- case x < b
    by_cases h3 : x ≥ a
    · -- case a ≤ x < b
      rw [abs_of_nonneg (show x - a ≥ 0 by linarith), abs_of_nonpos (show x - b ≤ 0 by linarith)]
      constructor
      · -- prove a-b ≤ (x - a) - (b - x)
        nlinarith
      · -- prove (x - a) - (b - x) ≤ b - a
        nlinarith
    · -- case x < a
      rw [abs_of_nonpos (show x - a ≤ 0 by linarith), abs_of_nonpos (show x - b ≤ 0 by linarith)]
      constructor
      · -- prove a-b ≤ (a - x) - (b - x)
        nlinarith
      · -- prove (a - x) - (b - x) ≤ b - a
        nlinarith