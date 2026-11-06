import Mathlib

theorem algebra_193673 (a : ℝ) (h : ∃ x y, x > 0 ∧ y > 0 ∧ x ≠ y ∧ x^2 - 2 * a * x + a = 0 ∧ y^2 - 2 * a * y + a = 0) :
    a ≥ 1 := by
  rcases h with ⟨x, y, hx, hy, hxy, hx2, hy2⟩

  have h1 : x^2 - y^2 = 2 * a * (x - y) := by linarith [hx2, hy2]

  have h2 : x - y ≠ 0 := by
    intro h'
    apply hxy
    linarith

  have h3 : x + y = 2 * a := by
    apply (mul_left_inj' h2).mp
    linarith [h1]

  have h4 : (x - y) ^ 2 > 0 := by
    apply sq_pos_of_ne_zero
    intro h'
    apply hxy
    linarith

  have h5 : 4 * a^2 - 4 * a > 0 := by
    nlinarith [h3, h4]

  nlinarith [sq_nonneg (a - 1)]