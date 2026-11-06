import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155282 (f : ℝ → ℝ) (hf : f = λ x => sin (3 * x)) (x : ℝ) (hx : x = π / 9) :
    deriv f x = 3 / 2 := by
  rw [hf]
  rw [hx]
  have h1 : cos (3 * (π / 9)) = 1 / 2 := by
    have h2 : 3 * (π / 9) = π / 3 := by
      ring
    rw [h2]
    exact cos_pi_div_three
  simp [deriv_mul, deriv_id'', mul_comm] at *
  all_goals
    try linarith [h1]
    all_goals
      try tauto