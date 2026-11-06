import Mathlib

open Real

theorem algebra_270766 {f : ℝ → ℝ}
    (hf : ∀ x, f x = logb (1 / 3) ((2 * x ^ 2 + 2 * x * sqrt (x ^ 2 + 1) + 1) ^ x)) :
    Even f := by 
  use (fun x => (logb (1 / 3) ((2 * x ^ 2 + 2 * x * sqrt (x ^ 2 + 1) + 1) ^ x)) / 2 )
  funext x
  rw [hf x]
  all_goals field_simp <;> ring