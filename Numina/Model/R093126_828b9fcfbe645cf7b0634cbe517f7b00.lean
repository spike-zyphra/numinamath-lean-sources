import Mathlib

theorem algebra_4166 {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a / 2 = 4 * b / 3) (h' : 4 * b / 3 = 5 * c / 6) :
    a / b = 40 / 15 ∧ b / c = 15 / 24 := by
  have ha1 : a = 8 * b / 3 := by
    linarith
  have h1 : a / b = 8 / 3 := by
    rw [ha1]
    field_simp [hb]
    <;> linarith
  have h2 : a / b = 40 / 15 := by
    rw [h1]
    norm_num
  have h3 : 8 * b = 5 * c := by
    linarith [h']
  have h4 : b / c = 5 / 8 := by
    have hc' : c ≠ 0 := hc
    field_simp [hc']
    linarith [h3]
  have h5 : b / c = 15 / 24 := by
    rw [h4]
    norm_num
  constructor
  · exact h2
  · exact h5