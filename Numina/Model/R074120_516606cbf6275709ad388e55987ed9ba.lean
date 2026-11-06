import Mathlib

open Real Set
open scoped Real

theorem calculus_13708 : IsLeast {x | 0 < x ∧ x < π / 2 ∧ sin (2 * x) * sin (3 * x) = cos (2 * x) * cos (3 * x)} (π / 10) := by
  constructor
  · -- Verify that π / 10 is in the set
    constructor
    · -- Show 0 < π / 10
      positivity
    constructor
    · -- Show π / 10 < π / 2
      have h : π > 0 := by positivity
      linarith
    · -- Verify equation
      have h1 : sin (2 * (π / 10)) * sin (3 * (π / 10)) = cos (2 * (π / 10)) * cos (3 * (π / 10)) := by
        have h2 : cos (2 * (π / 10)) * cos (3 * (π / 10)) - sin (2 * (π / 10)) * sin (3 * (π / 10)) = 0 := by
          have h3 : cos (2 * (π / 10)) * cos (3 * (π / 10)) - sin (2 * (π / 10)) * sin (3 * (π / 10)) = cos (2 * (π / 10) + 3 * (π / 10)) := by
            rw [cos_add]
            <;> ring
          rw [h3]
          have h4 : 2 * (π / 10) + 3 * (π / 10) = π / 2 := by
            linarith [Real.pi_pos]
          rw [h4]
          norm_num
        linarith [h2]
      linarith [h1]
  · -- Show π / 10 is the minimal
    intro x hx
    rcases hx with ⟨hx_pos, hx_lt, heq⟩
    by_contra h
    push_neg at h
    have heq2 : cos (5 * x) = 0 := by
      have h2 : sin (2 * x) * sin (3 * x) - cos (2 * x) * cos (3 * x) = 0 := by linarith [heq]
      have h1 : cos (2 * x) * cos (3 * x) - sin (2 * x) * sin (3 * x) = cos (2 * x + 3 * x) := by
        rw [cos_add]
        <;> ring
      have h3 : cos (2 * x + 3 * x) = 0 := by
        have h4 : cos (2 * x) * cos (3 * x) - sin (2 * x) * sin (3 * x) = 0 := by linarith [h2]
        linarith [h1, h4]
      have h5 : 2 * x + 3 * x = 5 * x := by ring
      rw [h5] at h3
      linarith
    have h6 : 5 * x < π / 2 := by
      nlinarith [Real.pi_pos, h, show x * 5 = 5 * x by linarith]
    have h7 : cos (5 * x) > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · -- Show 5x < π / 2
        linarith [h6, Real.pi_pos]
      · -- Show 0 < 5x
        nlinarith [show (0 : ℝ) < x from by linarith [hx_pos], Real.pi_pos]
    linarith [h7, heq2]