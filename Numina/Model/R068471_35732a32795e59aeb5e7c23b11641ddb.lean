import Mathlib

theorem algebra_236640 {a b c : ℝ} (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0)
    (h1 : (a + b) / c = (b + c) / a) (h2 : (b + c) / a = (a + c) / b) (h3 : b ≠ c) :
    a + b + c = 0 := by
  have eq1 : a * (a + b) = c * (b + c) := by
    have h4 : a ≠ 0 := h
    have h5 : c ≠ 0 := h''
    field_simp [h4, h5] at h1
    linarith
  have eq2 : b * (b + c) = a * (a + c) := by
    have h6 : a ≠ 0 := h
    have h7 : b ≠ 0 := h'
    field_simp [h6, h7] at h2
    linarith
  have eq3 : (b - c) * (a + b + c) = 0 := by
    nlinarith [eq1, eq2]
  cases (mul_eq_zero.mp eq3) with
  | inl h4 =>
    exfalso
    apply h3
    linarith
  | inr h5 =>
    linarith