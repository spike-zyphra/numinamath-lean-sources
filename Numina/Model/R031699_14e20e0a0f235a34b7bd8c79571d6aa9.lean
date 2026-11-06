import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_264818 {f : ℝ → ℝ} (hf : f = λ x => 1 / x) :
    ∃ x₀, f (x₀ + 1) = f x₀ + f 1 ↔ False := by 
  use 1
  have eq1 : f 1 = 1 := by 
    rw [hf]
    all_goals norm_num
  have eq2 : f (1 + 1) = 1 / 2 := by 
    rw [hf]
    all_goals norm_num 
  -- The goal is f (1 + 1) = f 1 + f 1 ↔ False
  have h3 : f (1 + 1) = f 1 + f 1 ↔ False := by 
    rw [eq2, eq1]
    norm_num 
  exact h3