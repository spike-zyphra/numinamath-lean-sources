import Mathlib

theorem algebra_246928 (d : ℝ) (h : d > 0) (h1 : d / 5.94 = d / 3.87 - 11.5) :
    round d = 128 := by
  have eq1 : d = (11.5 * 5.94 * 3.87) / 2.07 := by
    field_simp at h1 ⊢
    ring_nf at h1 ⊢
    nlinarith
  have h2 : round d = 128 := by
    rw [round_eq, Int.floor_eq_iff]
    constructor
    · -- Show that 128 ≤ d + 1/2
      rw [show d + (1 / (2 : ℝ)) = d + 0.5 by norm_num]
      have h3 : d = (11.5 * 5.94 * 3.87) / 2.07 := eq1
      rw [h3]
      norm_num
    · -- Show that d + 1/2 < 128 + 1
      rw [show d + (1 / (2 : ℝ)) = d + 0.5 by norm_num]
      have h3 : d = (11.5 * 5.94 * 3.87) / 2.07 := eq1
      rw [h3]
      norm_num
  exact h2