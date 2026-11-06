import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_277761 :
  IsLeast {f | ∃ x y : ℝ, f = (1 - y)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2} (1 / 6) := by
  constructor
  · -- Show 1/6 is in the set
    use 5 / 2, 5 / 6 
    norm_num 
  · -- Show 1/6 is the least value in the set
    intro f hf 
    rcases hf with ⟨x, y, h⟩ 
    rw [h]
    have h1 : (1 - y)^2 + (x + y - 3)^2 + (2 * x + y - 6)^2 ≥ 1 / 6 := by 
      nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (y - 5 / 6), 
          sq_nonneg ( (1 - y) - (1/6) ), sq_nonneg ( (x + y - 3) - (1/3) ), 
          sq_nonneg ( (2 * x + y - 6) - (-1/6) ), sq_nonneg (x - 5 / 2), sq_nonneg (y - 5 / 6)]
    linarith