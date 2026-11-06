import Mathlib

theorem inequalities_325124 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) (l : ℝ) (h : 0 < l ∧ l ≤ 1) :
    2 / (a * b - l) ≤ 1 / (a ^ 2 - l) + 1 / (b ^ 2 - l) := by
  have h1 : 0 < l := h.1
  have h2 : l ≤ 1 := h.2

  have ha2 : a ^ 2 > 1 := by nlinarith
  have hb2 : b ^ 2 > 1 := by nlinarith
  have hab : a * b > 1 := by nlinarith

  have ha2_sub_l : a ^ 2 - l > 0 := by nlinarith
  have hb2_sub_l : b ^ 2 - l > 0 := by nlinarith
  have hab_sub_l : a * b - l > 0 := by nlinarith

  have h4 : (b ^ 2 - l) * (a * b - l) + (a ^ 2 - l) * (a * b - l) - 2 * (a ^ 2 - l) * (b ^ 2 - l) ≥ 0 := by
    have h5 : (b ^ 2 - l) * (a * b - l) + (a ^ 2 - l) * (a * b - l) - 2 * (a ^ 2 - l) * (b ^ 2 - l) =
              (a - b) ^ 2 * (a * b + l) := by
      nlinarith
    rw [h5]
    have h6 : a * b > 1 := by nlinarith
    have h7 : a * b + l > 0 := by nlinarith
    nlinarith [sq_nonneg (a - b), h7]

  have h5 : 1 / (a ^ 2 - l) + 1 / (b ^ 2 - l) - 2 / (a * b - l) ≥ 0 := by
    have h6 : 1 / (a ^ 2 - l) + 1 / (b ^ 2 - l) - 2 / (a * b - l) =
        ((b ^ 2 - l) * (a * b - l) + (a ^ 2 - l) * (a * b - l) - 2 * (a ^ 2 - l) * (b ^ 2 - l)) / ((a ^ 2 - l) * (b ^ 2 - l) * (a * b - l)) := by
      field_simp
      <;> ring
    rw [h6]
    apply div_nonneg
    linarith
    all_goals
    positivity

  linarith