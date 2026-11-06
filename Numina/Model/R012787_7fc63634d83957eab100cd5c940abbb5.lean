import Mathlib

theorem algebra_237692 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 14 = b * 30) (h2 : a * 12 = b * 19) :
    a = 10 ∧ b = 10 := by
  have h3 : a * 14 = b * 30 := h1
  have h4 : a * 12 = b * 19 := h2
  have h5 : a * 7 = b * 15 := by
    linarith
  have h6 : a * 12 = b * 19 := h4
  nlinarith