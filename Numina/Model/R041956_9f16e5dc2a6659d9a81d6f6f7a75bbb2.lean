import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_148968 {f : ℝ → ℝ} (hf : f = λ x => x^2 * (2 - x)) :
    MonotoneOn f {x | 0 < x ∧ x < 4 / 3} := by
  intro x hx y hy hxy
  have h1 : 0 < x := hx.1
  have h2 : x < 4 / 3 := hx.2
  have h3 : 0 < y := hy.1
  have h4 : y < 4 / 3 := hy.2
  have h5 : x ≤ y := hxy
  have h6 : f x ≤ f y := by
    rw [hf]
    have h7 : (x : ℝ) ^ 2 * (2 - x) ≤ (y : ℝ) ^ 2 * (2 - y) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), 
          sq_nonneg (x - 4 / 3), sq_nonneg (y - 4 / 3), 
          mul_pos h1 h3, mul_pos h1 (show 0 < 4 / 3 - x by linarith), 
          mul_pos h3 (show 0 < 4 / 3 - y by linarith), 
          mul_nonneg (show 0 ≤ y - x by linarith) 
            (show 0 ≤ 4 / 3 - y by linarith), 
          mul_nonneg (show 0 ≤ x by linarith) 
            (show 0 ≤ 4 / 3 - x by linarith), 
          mul_self_nonneg (x - y), 
          mul_self_nonneg (x - 2 * y / 3)]
    simpa using h7
  exact h6