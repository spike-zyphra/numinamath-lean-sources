import Mathlib

open Real

theorem algebra_20570 :
  IsGreatest {r : ℤ | 0 < r ∧ 2 * π * r ≤ 60} 9 := by
  constructor
  · -- Show 9 is in the set
    constructor
    · -- Show 0 < (9 : ℤ)
      norm_num
    · -- Show 2 * π * (9 : ℤ) ≤ (60 : ℝ)
      have h1 : (2 * π * (9 : ℝ) ≤ (60 : ℝ)) := by
        have h2 : π ≤ (3.1416 : ℝ) := by linarith [pi_lt_31416]
        nlinarith [pi_pos]
      exact_mod_cast h1
  · -- Show that 9 is greatest in the set
    intro r hr
    rcases hr with ⟨hr_pos, hr_circumference⟩
    by_contra h
    push_neg at h
    have h2 : r ≥ 10 := by omega
    have h3 : (r : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h2
    have h4 : 2 * π * (r : ℝ) > (60 : ℝ) := by
      nlinarith [h3, Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
    linarith [hr_circumference, h4]