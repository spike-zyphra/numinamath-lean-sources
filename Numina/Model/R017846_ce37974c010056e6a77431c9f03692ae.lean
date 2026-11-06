import Mathlib

theorem algebra_177657 {a b c : ℝ} (ha : a ≠ 0) (hroots : ∃ x y, x^2*a+b*x+c=0 ∧ y^2*a+b*y+c=0 ∧ |x^3-y^3| = 2011) :
    ∃ x y, x^2*a+2*b*x+4*c=0 ∧ y^2*a+2*b*y+4*c=0 := by
  rcases hroots with ⟨x, y, hx, hy, h1⟩
  use 2 * x
  use 2 * y
  constructor
  · -- Show that (2 * x) ^ 2 * a + 2 * b * (2 * x) + 4 * c = 0
    have eq1 : (2 * x) ^ 2 * a + 2 * b * (2 * x) + 4 * c = 0 := by
      have eq2 : x ^ 2 * a + b * x + c = 0 := by linarith
      nlinarith
    linarith
  · -- Show that (2 * y) ^ 2 * a + 2 * b * (2 * y) + 4 * c = 0
    have eq2 : (2 * y) ^ 2 * a + 2 * b * (2 * y) + 4 * c = 0 := by
      have eq3 : y ^ 2 * a + b * y + c = 0 := by linarith
      nlinarith
    linarith