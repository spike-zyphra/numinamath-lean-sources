import Mathlib

theorem algebra_13479 :
    IsGreatest {v : ℝ | ∃ x y : ℝ, (2 * (x ^ 2 + y ^ 2) = x + y ∧ v = x - y)} (1 / 2 : ℝ) := by
  constructor
  · -- Show that 1/2 is in the set
    use 1 / 2, (0 : ℝ)
    constructor
    · norm_num 
    · norm_num 
  · -- Show that 1/2 is the greatest element in the set 
    intro v hv 
    rcases hv with ⟨x, y, h1, h2⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 0), sq_nonneg (x + y - 1), sq_nonneg (x - y - 1 / 2)]