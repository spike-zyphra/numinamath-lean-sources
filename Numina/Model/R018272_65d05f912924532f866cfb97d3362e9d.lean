import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_178145 (f : ℝ → ℝ) (hf : f = λ x => arctan (1 / x)) (x : ℝ) (hx : x = 1) :
    deriv f x * (-0.1) = 0.05 := by 
  rw [hf]
  rw [hx] -- Substitute x = 1 
  have eq1 : deriv (fun (y : ℝ) => arctan (1 / y)) 1 = -1 / 2 := by 
    simp [deriv_comp, Real.deriv_arctan, differentiableAt_id', differentiableAt_inv, differentiableAt_arctan]
    all_goals 
      field_simp 
      <;> norm_num 
  rw [eq1] 
  all_goals
    norm_num