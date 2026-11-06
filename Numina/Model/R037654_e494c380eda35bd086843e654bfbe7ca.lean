import Mathlib

theorem inequalities_36188 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    (1 + 1 / x) * (1 + 1 / y) ≥ 9 := by

  have h1 : y = 1 - x := by linarith

  have h2 : x * y > 0 := by
    apply mul_pos
    exact hx
    exact hy

  have h4 : x * y ≤ (1 / 4 : ℝ) := by
    have h5 : y = 1 - x := by linarith
    rw [h5]
    have h6 : x * (1 - x) ≤ (1 / 4 : ℝ) := by
      have h7 : (x - (1 / 2)) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    nlinarith

  have h5 : (1 + 1 / x) * (1 + 1 / y) - 9 ≥ 0 := by
    have h6 : (1 + 1 / x) * (1 + 1 / y) - 9 =
        ( (x + 1) * (y + 1) - 9 * (x * y) ) / (x * y) := by
      field_simp
      <;> ring
    rw [h6]

    have h7 : (x + 1) * (y + 1) - 9 * (x * y) ≥ 0 := by
      have h8 : (x + 1) * (y + 1) - 9 * (x * y) =
          -8 * (x * y) + (x + y) + 1 := by ring
      rw [h8]
      have h9 : x + y = 1 := hxy
      have h10 : -8 * (x * y) + (x + y) + 1 ≥ 0 := by
        have h11 : x * y ≤ (1 / 4 : ℝ) := h4
        nlinarith
      linarith

    apply div_nonneg
    linarith
    all_goals
      positivity

  linarith