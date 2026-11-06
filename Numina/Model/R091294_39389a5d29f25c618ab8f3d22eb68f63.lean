import Mathlib

theorem algebra_129767 {f : ℝ → ℝ} (hf : ∀ x, f x = 4 ^ x) :
    ∀ x, f (x + 1) - f x = 3 * f x := by
  intro x
  have h1 : f (x + 1) = 4 ^ (x + 1 : ℝ) := hf (x + 1)
  have h2 : f x = 4 ^ (x : ℝ) := hf x
  rw [h1, h2]
  have h3 : (4 : ℝ) ^ (x + 1 : ℝ) = (4 : ℝ) ^ (x : ℝ) * (4 : ℝ) := by
    rw [Real.rpow_add]
    all_goals norm_num
    all_goals norm_num
  rw [h3]
  ring