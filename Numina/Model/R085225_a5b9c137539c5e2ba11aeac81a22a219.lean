import Mathlib

theorem algebra_321160 (a : ℝ) (h : ∃ x y, x > 0 ∧ y > 0 ∧ y = a * x + 3 * a + 2 ∧ y = -3 * x + 3) :
    a ∈ Set.Ioo (-1 / 2) (1 / 3) := by
  rcases h with ⟨x, y, hx1, hy1, h1, h2⟩

  have eq1 : a * x + 3 * a + 2 = -3 * x + 3 := by
    nlinarith

  have hx2 : x * (a + 3) = 1 - 3 * a := by
    linarith

  have h3 : a + 3 > 0 := by
    nlinarith [hx1, hx2]

  have h4 : 1 - 3 * a > 0 := by
    nlinarith [hx1, hx2, h3]

  have h5 : a < 1 / 3 := by
    linarith

  have h7 : a * x + 3 * a + 2 > 0 := by
    linarith

  have h8 : -3 * x + 3 > 0 := by
    linarith

  have h9 : a > -1 / 2 := by
    nlinarith [hx1, h3, h7, h8]

  constructor
  · -- prove a > -1/2
    linarith
  · -- prove a < 1/3
    linarith