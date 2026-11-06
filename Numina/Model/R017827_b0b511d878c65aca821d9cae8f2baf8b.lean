import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_237361 : IsLeast {y : ℝ | ∃ x, y = cos (4 * x) + 6 * cos (3 * x) + 17 * cos (2 * x) + 30 * cos x} (-18) := by
  constructor
  · -- Show that -18 is in the set
    use Real.pi
    have h1 : cos (4 * Real.pi) = 1 := by
      have h3 : cos (4 * Real.pi) = 1 := by
        have h4 : 4 * Real.pi = 2 * Real.pi + 2 * Real.pi := by ring
        rw [h4]
        have h5 : cos (2 * Real.pi + 2 * Real.pi) = cos (2 * Real.pi + 2 * Real.pi) := by rfl
        have h6 : cos (2 * Real.pi + 2 * Real.pi) = cos (2 * Real.pi) := by
          rw [show 2 * Real.pi + 2 * Real.pi = 2 * Real.pi + (2 * Real.pi) by ring]
          rw [cos_add, cos_two_pi, sin_two_pi]
          all_goals norm_num
        rw [h6]
        have h7 : cos (2 * Real.pi) = 1 := Real.cos_two_pi
        linarith
      linarith

    have h2 : cos (3 * Real.pi) = -1 := by
      have h3 : 3 * Real.pi = 2 * Real.pi + Real.pi := by ring
      rw [h3]
      have h4 : cos (2 * Real.pi + Real.pi) = cos (Real.pi) := by
        rw [cos_add, cos_two_pi, sin_two_pi]
        all_goals norm_num
      have h5 : cos (Real.pi) = -1 := Real.cos_pi
      rw [h4, h5]

    have h3 : cos (2 * Real.pi) = 1 := Real.cos_two_pi
    have h4 : cos Real.pi = -1 := Real.cos_pi

    rw [h1, h2, h3, h4]
    norm_num

  · -- Show that -18 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩

    have h1 : cos (4 * x) = 8 * cos x ^ 4 - 8 * cos x ^ 2 + 1 := by
      have h2 : cos (4 * x) = 2 * (cos (2 * x)) ^ 2 - 1 := by
        rw [show 4 * x = 2 * (2 * x) by ring]
        rw [cos_two_mul]
      have h3 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
        rw [cos_two_mul]
      rw [h2, h3]
      ring

    have h2 : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
      rw [cos_three_mul]

    have h3 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
      rw [cos_two_mul]

    have h4 : cos (4 * x) + 6 * cos (3 * x) + 17 * cos (2 * x) + 30 * cos x ≥ -18 := by
      have h5 : cos (4 * x) = 8 * cos x ^ 4 - 8 * cos x ^ 2 + 1 := h1
      have h6 : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := h2
      have h7 : cos (2 * x) = 2 * cos x ^ 2 - 1 := h3
      rw [h5, h6, h7]
      nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x + 1 / 2), sq_nonneg (cos x * (cos x + 1)), sq_nonneg (cos x * 1), Real.cos_sq_add_sin_sq x]

    linarith [h4, hx]