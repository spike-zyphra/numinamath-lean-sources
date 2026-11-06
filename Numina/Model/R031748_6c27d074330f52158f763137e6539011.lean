import Mathlib

theorem algebra_215768 :
    IsGreatest {x | ∃ a b : ℝ, x = a^2 * b - b^2 * a ∧ a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1} (1 / 4) := by
  constructor
  · -- Show that 1 / 4 is indeed achievable, with a = 1 and b = 1 / 2.
    use 1, 1 / 2 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · norm_num 
  · -- Show that 1 / 4 is the greatest such value.
    intro w hw 
    rcases hw with ⟨a, b, heq1, ha, hb⟩
    rw [Set.mem_Icc] at ha hb 
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a - b), mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr ha.2), mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hb.2), mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr hb.1), mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)]