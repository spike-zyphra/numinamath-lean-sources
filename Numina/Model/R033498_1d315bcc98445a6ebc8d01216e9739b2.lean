import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13547 {f : ℝ → ℝ}
  (hf : f = λ x => if x > 4 then sqrt x else x ^ 2) :
  f (f (f 2)) = 4 := by
  have h1 : f 2 = 4 := by 
    rw [hf]
    norm_num
  have h2 : f 4 = 16 := by 
    rw [hf]
    norm_num
  have h3 : f 16 = 4 := by
    rw [hf]
    norm_num
    <;> try { 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    }
  rw [h1]
  rw [h2]
  exact h3