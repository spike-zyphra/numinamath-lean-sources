import Mathlib

open Finset

theorem algebra_229645 {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hxn : ∀ n, x (n + 1) = ((n ^ 2 + n + 1) * x n + 1) / (n ^ 2 + n + 1 - x n)) :
    x 8453 = 8453 := by

  have h1 : ∀ (n : ℕ), x n = (↑n : ℝ) := by
    intro n 
    induction n with 
    | zero => 
      rw [hx0]
      all_goals norm_num 
    | succ n ih => 
      have eq1 := hxn n 
      rw [eq1]
      rw [ih]
      field_simp [(show ((↑n : ℝ) ^ 2 + 1) ≠ 0 by 
          have h1 : ((↑n : ℝ) ^ 2 + 1) > 0 := by 
            nlinarith [show (0 : ℝ) ≤ (↑n : ℝ) by positivity]
          linarith
        ), (show ((↑n : ℝ) ^ 2 + (↑n : ℝ) + 1 - (↑n : ℝ)) ≠ 0 by 
          have h2 : (↑n : ℝ) ^ 2 + (↑n : ℝ) + 1 - (↑n : ℝ) = (↑n : ℝ) ^ 2 + 1 := by ring 
          rw [h2]
          have h1 : ((↑n : ℝ) ^ 2 + 1) > 0 := by 
            nlinarith [show (0 : ℝ) ≤ (↑n : ℝ) by positivity]
          linarith
        )]
      <;> ring_nf 
      <;> norm_num
  have h2 := h1 8453 
  norm_num at h2 ⊢ 
  all_goals linarith