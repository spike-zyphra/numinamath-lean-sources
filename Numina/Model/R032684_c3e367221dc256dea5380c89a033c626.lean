import Mathlib

theorem algebra_9065 :
  IsLeast {z : ℝ | ∃ x y, z = 5 * x ^ 2 + 4 * y ^ 2 - 8 * x * y + 2 * x + 4} 3 := by 
  constructor
  · -- Show 3 is in the set
    use -1, -1
    norm_num
  · -- Show 3 is the least
    intro z h
    rcases h with ⟨x, y, hz⟩
    have h : 5 * x ^ 2 + 4 * y ^ 2 - 8 * x * y + 2 * x + 4 ≥ 3 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), 
          sq_nonneg (x - y), sq_nonneg ((x + 1) + (y + 1)), 
          sq_nonneg (x + 1 - (y + 1)), sq_nonneg (2 * (x + 1) - (y + 1)), 
          sq_nonneg (2 * (x + 1) + (y + 1))]
    linarith [h, hz]