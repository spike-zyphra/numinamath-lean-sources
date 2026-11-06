import Mathlib

theorem algebra_11246 : IsLeast {z : ℝ | ∃ x y, z = x^2 + y^2 - 6 * x + 4 * y + 18} 5 := by
  constructor
  · -- Show that 5 is in the set, with specific x and y
    use 3, -2
    norm_num
  · -- Show that 5 is the least element in the set
    intro z h
    rcases h with ⟨x, y, h_eq⟩
    -- Prove that z >= 5 by transforming the expression with completed square form.
    have h : x^2 + y^2 - 6 * x + 4 * y + 18 = (x - 3)^2 + (y + 2)^2 + 5 := by
      ring
    rw [h] at h_eq
    have h1 : (x - 3)^2 + (y + 2)^2 ≥ 0 := by
      apply add_nonneg
      · apply pow_two_nonneg
      · apply pow_two_nonneg
    linarith