import Mathlib

theorem algebra_240260 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : (1 + 40 / 100) * x + (1 + 60 / 100) * y = (1 + 54 / 100) * (x + y)) :
    ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ x / y = a / b ∧ 11 * a + 13 * b = 124 := by
  have h1 : 140 * x + 160 * y = 154 * (x + y) := by
    nlinarith
  have h2 : 6 * y = 14 * x := by
    nlinarith [h1]
  have h3 : 3 * y = 7 * x := by
    nlinarith [h2]
  use 3
  use 7
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · -- x / y = 3 / 7
    have h4 : x / y = (3 : ℝ) / 7 := by
      have h5 : y > 0 := hy
      have h6 : x = (3 / 7) * y := by
        nlinarith [h3]
      have h7 : x / y = (3 / 7 : ℝ) := by
        rw [h6]
        field_simp [h5]
        <;> nlinarith
      linarith
    norm_num at h4 ⊢
    exact h4
  · -- compute 11 * 3 + 13 * 7 = 124
    norm_num