import Mathlib

theorem algebra_209091 :
    IsLeast {z : ℝ | ∃ x y : ℝ, z = 4 + x^2 * y^4 + x^4 * y^2 - 3 * x^2 * y^2} 3 := by
  constructor
  · -- Show 3 is in the set
    use 1, 1
    norm_num
  · -- Show for all z in the set, 3 ≤ z
    intro z h
    rcases h with ⟨x, y, hz⟩
    have h1 : 4 + x^2 * y^4 + x^4 * y^2 - 3 * x^2 * y^2 ≥ 3 := by
      nlinarith [sq_nonneg (x^2 * y^2 - 1), sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (x * y), sq_nonneg (x^2 * (y^2 - 1)), sq_nonneg (y^2 * (x^2 - 1)), mul_nonneg (sq_nonneg x) (sq_nonneg y), mul_nonneg (sq_nonneg (x^2 - 1)) (sq_nonneg (y^2 - 1)), mul_nonneg (sq_nonneg x) (sq_nonneg y) ]
    linarith [hz, h1]