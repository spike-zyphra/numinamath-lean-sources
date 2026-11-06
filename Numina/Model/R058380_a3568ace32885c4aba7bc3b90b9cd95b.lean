import Mathlib

theorem algebra_319235 (x1 x2 y1 y2 x0 y0 : ℝ)
    (h₁ : x1 + 2 * y1 - 1 = 0) (h₂ : x2 + 2 * y2 + 3 = 0)
    (h₃ : (x1 + x2) / 2 = x0 ∧ (y1 + y2) / 2 = y0)
    (h₄ : y0 > x0 + 2) :
    -1 / 2 < y0 / x0 ∧ y0 / x0 < -1 / 5 := by

  rcases h₃ with ⟨hx, hy⟩

  have hx1 : x1 = 1 - 2 * y1 := by linarith
  have hx2 : x2 = -3 - 2 * y2 := by linarith

  have hx0 : x0 = -1 - 2 * y0 := by
    have h1 : x1 + x2 = 2 * x0 := by linarith
    rw [hx1, hx2] at h1
    nlinarith [hy]

  have h5 : y0 > 1 / 3 := by
    nlinarith [h₄, hx0]

  constructor
  · -- Prove that $\frac{y_0}{x_0} > -\frac{1}{2}$
    rw [show x0 = -1 - 2 * y0 by linarith [hx0]]
    apply (lt_div_iff_of_neg' (by nlinarith )).mpr
    nlinarith

  · -- Prove that $\frac{y_0}{x_0} < -\frac{1}{5}$
    rw [show x0 = -1 - 2 * y0 by linarith [hx0]]
    apply (div_lt_iff_of_neg' (by nlinarith )).mpr
    nlinarith