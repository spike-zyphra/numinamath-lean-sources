import Mathlib

theorem calculus_14625 : ∃ n : ℕ, n ≤ 180 ∧ Real.cos (n * Real.pi / 180) = Real.cos (758 * Real.pi / 180) := by
  use 38
  constructor
  · -- Show that 38 ≤ 180
    norm_num
  · -- Show that cos(38 * π / 180) = cos(758 * π / 180)
    have h1 : Real.cos (38 * Real.pi / 180) = Real.cos (758 * Real.pi / 180) := by
      have h2 : 758 * Real.pi / 180 = 38 * Real.pi / 180 + 4 * Real.pi := by 
        ring_nf
      rw [h2]
      have h3 : Real.cos (38 * Real.pi / 180 + 4 * Real.pi) = Real.cos (38 * Real.pi / 180) := by
        have h5 : Real.cos (38 * Real.pi / 180 + 4 * Real.pi) = Real.cos (38 * Real.pi / 180 + 2 * Real.pi + 2 * Real.pi) := by ring_nf
        rw [h5]
        have h6 : Real.cos (38 * Real.pi / 180 + 2 * Real.pi + 2 * Real.pi) = Real.cos (38 * Real.pi / 180 + 2 * Real.pi) := by 
          rw [show 38 * Real.pi / 180 + 2 * Real.pi + 2 * Real.pi = (38 * Real.pi / 180 + 2 * Real.pi) + 2 * Real.pi by ring]
          rw [Real.cos_add_two_pi]
        have h7 : Real.cos (38 * Real.pi / 180 + 2 * Real.pi) = Real.cos (38 * Real.pi / 180) := by 
          rw [show 38 * Real.pi / 180 + 2 * Real.pi = (38 * Real.pi / 180) + 2 * Real.pi by ring]
          rw [Real.cos_add_two_pi]
        rw [h6, h7]
      linarith [h3]
    exact h1