import Mathlib

theorem algebra_4210 {a b : ℝ} (h₀ : a * b = 1) (h₁ : a + b = 2019) :
    (a^2 - 2019 * a + 1) * (b^2 - 2019 * b + 1) = 0 := by
  have eq1 : a^2 - 2019 * a + 1 = 0 := by
    have h2 : (2019 : ℝ) = a + b := by
      linarith
    rw [h2] at *
    have eq2 : a ^ 2 - (a + b) * a + 1 = 0 := by
      have h3 : a * (b) = 1 := h₀
      have h4 : a^2 - (a + b) * a + 1 = 1 - (a * b) := by
        nlinarith
      rw [h4, h3]
      norm_num
    linarith
  rw [eq1]
  norm_num