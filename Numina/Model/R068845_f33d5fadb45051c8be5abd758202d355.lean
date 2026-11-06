import Mathlib

theorem algebra_238851 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : ∃ x, x > a ∧ x < b ∧ b - x = a - x + c - b) (h2 : ∃ y, y > b ∧ y < c ∧ c - y = b - y + 25)
    (h3 : b - a = c - b - 5) :
    c - a = 3 := by
  rcases h1 with ⟨x, hx1, hx2, hx3⟩
  rcases h2 with ⟨y, hy1, hy2, hy3⟩
  linarith