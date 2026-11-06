import Mathlib

open Real

theorem algebra_154906 {φ : ℝ → ℝ} (hφ : φ = fun x => cos (2 * x) / (x ^ ((1 : ℝ) / 3) + 3 * x)) :
    Odd φ := by

  unfold Odd
  use (fun x => (φ x - 1) / 2 )
  funext x
  simp [hφ]
  <;> ring