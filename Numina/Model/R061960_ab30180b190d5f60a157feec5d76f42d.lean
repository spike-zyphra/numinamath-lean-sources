import Mathlib

theorem algebra_122697 (a b c : ℝ) (ha : a ≠ 0) (hroots : ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧
    x^3 + a * x^2 + b * x + c = 0 ∧ y^3 + a * y^2 + b * y + c = 0 ∧ z^3 + a * z^2 + b * z + c = 0)
    (hecc : ∃ e1 e2 e3, e1 > 0 ∧ e2 > 0 ∧ e3 > 0 ∧ e1 + e2 + e3 = 1 ∧ e1 * e2 * e3 = 1) :
    b / a ∈ Set.Ioo (-2) (-1 / 2) := by 
  obtain ⟨e1, e2, e3, h1, h2, h3, he1, he2⟩ := hecc
  nlinarith [mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3, 
          sq_nonneg (e1 - e2), sq_nonneg (e1 - e3), sq_nonneg (e2 - e3)]