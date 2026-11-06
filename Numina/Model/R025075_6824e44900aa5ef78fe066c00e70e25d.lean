import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_18934 {f : ℝ → ℝ}
  (hf : f = λ x => ((x - 1)^7 + 3*(x - 1)^6 + (x - 1)^5 + 1)/(x - 1)^5) :
  IsLeast {y | ∃ x, x > 1 ∧ f x = y} 6 := by 
  constructor 
  · -- Show 6 is in the set
    use 2
    constructor
    · -- Show 2 > 1
      norm_num 
    · -- Show f 2 = 6 
      rw [hf]
      norm_num
  · -- Show 6 is the least element in the set
    intro y hy 
    rcases hy with ⟨x, hx, heq⟩
    rw [hf] at heq 
    have h1 : ((x - 1) ^ 7 + 3 * (x - 1) ^ 6 + (x - 1) ^ 5 + 1) / (x - 1) ^ 5 = y := heq 
    have h2 : x - 1 > 0 := by linarith 
    have h3 : ((x - 1) ^ 7 + 3 * (x - 1) ^ 6 + (x - 1) ^ 5 + 1) / (x - 1) ^ 5 ≥ 6 := by
      have h4 : (x - 1) ^ 5 > 0 := by positivity
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg ((x - 1) ^ 2 - 1), sq_nonneg ((x - 1) ^ 2 - (x - 1) ), sq_nonneg ((x - 1) - 1), 
          sq_nonneg ((x - 1) ^ 3 - (x - 1) ^ 2), sq_nonneg ((x - 1) ^ 3 - 1), sq_nonneg ((x - 1) ^ 2 - 1), 
          sq_nonneg ((x - 1) - 0), sq_nonneg ((x - 1) + 1), mul_pos (show x - 1 > 0 by linarith) (show x - 1 > 0 by linarith), 
          sq_nonneg ((x - 1) * ((x - 1) - 1)), sq_nonneg ((x - 1) ^ 5 - (x - 1) ^ 2), 
          sq_nonneg ((x - 1) ^ 4 - (x - 1) ^ 3)]
    linarith [h1, h3]