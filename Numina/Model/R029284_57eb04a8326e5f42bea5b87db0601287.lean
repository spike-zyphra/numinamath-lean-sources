import Mathlib

theorem algebra_3958 {a b : ℝ} (h₀ : 0 < a) (h₁ : 0 < b)
    (h₂ : a * b = 1) (h₃ : a + b = 2019) :
    (a^2 - 2020 * a + 1) * (b^2 - 2020 * b + 1) = 1 := by 
  have h4 : b = 1 / a := by
    field_simp
    nlinarith [h₂]
  have h5 : a^2 - 2019 * a + 1 = 0 := by
    nlinarith [h₂, h₃]
  have h6 : a^2 - 2020 * a + 1 = -a := by
    nlinarith [h5]
  have h7 : b^2 - 2020 * b + 1 = -1 / a := by
    rw [show b = 1 / a by linarith [h4]]
    have ha : a ≠ 0 := by nlinarith
    field_simp [ha]
    nlinarith [h5]
  have h8 : (a^2 - 2020 * a + 1) * (b^2 - 2020 * b + 1) = 1 := by
    rw [show a^2 - 2020 * a + 1 = -a by linarith [h6]]
    rw [show b^2 - 2020 * b + 1 = -1 / a by linarith [h7]]
    have ha : a ≠ 0 := by nlinarith
    field_simp [ha]
    <;> nlinarith
  exact h8