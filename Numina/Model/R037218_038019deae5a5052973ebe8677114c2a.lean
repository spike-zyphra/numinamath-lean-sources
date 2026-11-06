import Mathlib

theorem algebra_120863 {a b x: ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 3 ≤ x)
    (h1 : x / (a + b) = x / a - 40) (h2 : (x - 3) / (a + b) + 3 / a = x / a - 30) :
    x = 12 := by

  have h3 : 0 < a + b := by nlinarith
  have eq1 : x / (a + b) = x / a - 40 := h1
  have eq2 : (x - 3) / (a + b) + 3 / a = x / a - 30 := h2

  have eq3 : x * a = x * (a + b) - 40 * a * (a + b) := by
    have h4 : a ≠ 0 := by linarith
    have h5 : a + b ≠ 0 := by linarith
    field_simp [h4, h5] at eq1 ⊢
    nlinarith

  have eq4 : a * (x - 3) + 3 * (a + b) = x * (a + b) - 30 * a * (a + b) := by
    have h4 : a ≠ 0 := by linarith
    have h5 : a + b ≠ 0 := by linarith
    field_simp [h4, h5] at eq2 ⊢
    nlinarith

  have h5 : 40 * a ^ 2 + 40 * a * b = x * b := by
    nlinarith [eq3]

  have h7 : 3 * b + 30 * a ^ 2 + 30 * a * b = x * b := by 
    nlinarith [eq4]

  have h8 : 10 * a ^ 2 + 10 * a * b = 3 * b := by
    nlinarith [h5, h7]

  have h10 : x * b = 12 * b := by
    nlinarith [h5, h8]

  have h11 : (x - 12) * b = 0 := by
    nlinarith [h10]

  cases' (mul_eq_zero.1 h11) with h12 h13
  · -- x - 12 = 0
    linarith
  · -- b = 0
    nlinarith