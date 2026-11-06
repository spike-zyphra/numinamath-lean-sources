import Mathlib

theorem algebra_133932 (x y z : ℝ) (h1 : x + 5 * y + 2 * z - 5 = 0) (h2 : 2 * x - 5 * y - z + 5 = 0) :
    x / 5 = (y - 1) / 5 ∧ (y - 1) / 5 = z / -15 := by
  have h3 : z = -3 * x := by
    have eq1 : 3 * x + z = 0 := by
      linarith [h1, h2]
    linarith

  have h4 : y = x + 1 := by
    linarith [h1, h3]

  have h5 : x / 5 = (y - 1) / 5 := by
    have h6 : y - 1 = x := by
      linarith [h4]
    rw [h6]

  have h7 : (y - 1) / 5 = z / -15 := by
    have h6 : z = -3 * x := h3
    have h8 : y - 1 = x := by linarith [h4]
    rw [h6]
    rw [h8]
    all_goals linarith

  exact ⟨h5, h7⟩