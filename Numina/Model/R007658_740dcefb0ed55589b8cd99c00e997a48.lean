import Mathlib

theorem algebra_20809 {wage price : ℝ} (h1 : wage = 20000) (h2 : price = 66200) : IsLeast {rate : ℝ | 0 < rate ∧ wage * (1 + rate / 100) ^ 2 + wage * (1 + rate / 100) + wage ≥ price} 10 := by
  rw [h1, h2]
  constructor
  · -- Show 10 is in the set
    constructor
    · -- 0 < 10
      norm_num
    · -- Check inequality
      norm_num
  · -- Show no rate less than 10 is in the set
    intro rate hr
    rcases hr with ⟨hr_pos, hineq⟩
    by_contra h
    push_neg at h
    -- Show that rate < 10, then the inequality is not satisfied
    -- We will compute for rate < 10
    -- The total is 20000 * (1 + rate / 100)^2 + 20000 * (1 + rate / 100) + 20000 < 66200
    -- But Lean can handle the algebra
    nlinarith [sq_nonneg (rate - 10), sq_nonneg ((rate / 100) - 0.1), sq_nonneg ((rate / 100) + 1), sq_nonneg ((rate / 100) - 1), sq_nonneg ((rate / 100)), sq_nonneg (rate / 100 - 1 / 10)]