import Mathlib

open Polynomial Finset

theorem algebra_605959 :
  ∃ p q : Polynomial ℝ,
    ∀ n : ℕ, n > 0 → 
      (∑ i in Icc 1 n, eval (i : ℝ) p) = eval (n : ℝ) p * eval (n : ℝ) q := by
  use (0 : Polynomial ℝ)
  use (1 : Polynomial ℝ)
  intro n hn
  have eq1 : (∑ i in Icc 1 n, eval (i : ℝ) (0 : Polynomial ℝ)) = 0 := by 
    simp
  have eq2 : eval (n : ℝ) (0 : Polynomial ℝ) * eval (n : ℝ) (1 : Polynomial ℝ) = 0 := by 
    simp
  rw [eq1, eq2]
  all_goals norm_num