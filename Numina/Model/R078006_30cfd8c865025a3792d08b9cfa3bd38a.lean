import Mathlib

theorem algebra_2453
    (x : ℝ)
    (hx : -0.5 < x ∧ x < 1) :
    |Real.sqrt ((2 * x + 1) ^ 2) - Real.sqrt ((x - 4) ^ 2)| = 3 - 3 * x := by
  have h1 : Real.sqrt ((2 * x + 1) ^ 2) = |2 * x + 1| := by
    rw [Real.sqrt_sq_eq_abs]
  have h2 : Real.sqrt ((x - 4) ^ 2) = |x - 4| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1, h2]

  have h3 : 2 * x + 1 > 0 := by
    have h4 : x > -0.5 := hx.left
    norm_num at h4 ⊢
    linarith

  have h4 : |2 * x + 1| = 2 * x + 1 := by
    rw [abs_of_pos h3]

  have h5 : x - 4 < 0 := by
    have h6 : x < 1 := hx.right
    linarith

  have h6 : |x - 4| = -(x - 4) := by
    rw [abs_of_neg h5]

  rw [h4, h6]

  have h7 : (2 * x + 1) - (-(x - 4)) = 3 * x - 3 := by
    ring

  rw [h7]

  have h8 : 3 * x - 3 < 0 := by
    have h9 : x < 1 := hx.right
    linarith

  rw [abs_of_neg h8]
  ring