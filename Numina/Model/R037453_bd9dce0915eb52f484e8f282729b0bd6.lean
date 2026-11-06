import Mathlib

theorem algebra_322808 {a b c : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 - 3 * x - 1 = 0 ∧ y^2 - 3 * y - 1 = 0 ∧
    x^4 + a * x^2 + b * x + c = 0 ∧ y^4 + a * y^2 + b * y + c = 0) :
    a + b - 2 * c = -13 := by
  rcases h with ⟨x, y, hxy, hx, hy, hx4, hy4⟩

  have h1 : x^2 = 3 * x + 1 := by linarith
  have h2 : y^2 = 3 * y + 1 := by linarith

  have h3 : x^3 = 10 * x + 3 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (3 * x + 1) := by rw [h1]
      _ = 3 * x^2 + x := by ring
      _ = 3 * (3 * x + 1) + x := by rw [h1]
      _ = 10 * x + 3 := by linarith

  have h4 : x^4 = 33 * x + 10 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (10 * x + 3) := by rw [h3]
      _ = 10 * x^2 + 3 * x := by ring
      _ = 10 * (3 * x + 1) + 3 * x := by rw [h1]
      _ = 33 * x + 10 := by linarith

  have h5 : y^3 = 10 * y + 3 := by
    calc
      y^3 = y * y^2 := by ring
      _ = y * (3 * y + 1) := by rw [h2]
      _ = 3 * y^2 + y := by ring
      _ = 3 * (3 * y + 1) + y := by rw [h2]
      _ = 10 * y + 3 := by linarith

  have h6 : y^4 = 33 * y + 10 := by
    calc
      y^4 = y * y^3 := by ring
      _ = y * (10 * y + 3) := by rw [h5]
      _ = 10 * y^2 + 3 * y := by ring
      _ = 10 * (3 * y + 1) + 3 * y := by rw [h2]
      _ = 33 * y + 10 := by linarith

  rw [h4] at hx4
  rw [h6] at hy4
  rw [h1] at hx4
  rw [h2] at hy4

  nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
    intro h'
    apply hxy
    linarith
  ), sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 2), sq_nonneg (y - 2)]