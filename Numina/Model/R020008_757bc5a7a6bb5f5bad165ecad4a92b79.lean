import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_195622 : IsGreatest {x | ∃ t : ℝ, t ∈ Ioo 0 Real.pi ∧ x = log (sin t)} 0 := by
  constructor
  · -- Show that 0 is in the set
    use Real.pi / 2
    constructor
    · -- Show that π/2 ∈ (0, π)
      constructor
      · -- Show that 0 < π/2
        linarith [Real.pi_pos]
      · -- Show that π/2 < π
        linarith [Real.pi_pos]
    · -- Show that log (sin (π / 2)) = 0
      have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      rw [h1]
      simp
  · -- Show that 0 is greatest in the set
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    rcases ht with ⟨ht1, ht2⟩
    have h1 : 0 < sin t := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_gt_three, ht1, ht2]
    have h2 : sin t ≤ 1 := by 
      apply sin_le_one
    have h3 : log (sin t) ≤ (0 : ℝ) := by
      have h4 : sin t ≤ (1 : ℝ) := by
        apply sin_le_one
      have h5 : log (sin t) ≤ log (1 : ℝ) := by
        apply Real.log_le_log
        all_goals nlinarith [h1, h4]
      have h6 : log (1 : ℝ) = 0 := by
        simp [Real.log_one]
      linarith [h5, h6]
    linarith