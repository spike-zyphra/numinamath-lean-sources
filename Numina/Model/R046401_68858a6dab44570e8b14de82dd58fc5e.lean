import Mathlib

theorem algebra_609863 {a d : ℝ} (ha : a ≠ 0) (h : a^2 - 6*a*d + 8*d^2 = 0) : (d/a = 1/2 ∨ d/a = 1/4) := by
  have h1 : (a - 2 * d) * (a - 4 * d) = 0 := by
    linarith

  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where a - 2d = 0, so a = 2d, hence d/a = 1/2.
    left
    have h4 : a = 2 * d := by linarith
    have h5 : d / a = 1 / 2 := by
      rw [show a = 2 * d by linarith]
      have h6 : (2 * d) ≠ 0 := by
        intro h7
        have h8 : a = 0 := by
          linarith
        contradiction
      field_simp [h6]
      <;> linarith
    exact h5
  · -- Case where a - 4d = 0, so a = 4d, hence d/a = 1/4.
    right
    have h7 : a = 4 * d := by linarith
    have h8 : d / a = 1 / 4 := by
      rw [show a = 4 * d by linarith]
      have h9 : (4 * d) ≠ 0 := by
        intro h10
        have h11 : a = 0 := by
          linarith
        contradiction
      field_simp [h9]
      <;> linarith
    exact h8