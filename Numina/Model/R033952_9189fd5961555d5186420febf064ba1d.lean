import Mathlib

open Real

theorem calculus_279038 (a : ℝ) (f : ℝ → ℝ) (hf : f = fun x => a * x^3) :
    ∀ x y, x < y → (a > 0 → f x < f y) ∧ (a < 0 → f x > f y) := by
  intro x y hxy
  constructor
  · -- Proof of (a > 0 → f x < f y)
    intro ha
    rw [hf]
    have h1 : (a * x ^ 3) < (a * y ^ 3) := by
      have h2 : x ^ 3 < y ^ 3 := by
        nlinarith [sq_pos_of_pos (show (0: ℝ) < (y - x) by linarith), sq_nonneg (y + x), sq_nonneg (y - x)]
      nlinarith
    simpa using h1
  · -- Proof of (a < 0 → f x > f y)
    intro ha
    rw [hf]
    have h1 : (a * x ^ 3) > (a * y ^ 3) := by
      have h2 : x ^ 3 < y ^ 3 := by
        nlinarith [sq_pos_of_pos (show (0: ℝ) < (y - x) by linarith), sq_nonneg (y + x), sq_nonneg (y - x)]
      nlinarith
    simpa using h1