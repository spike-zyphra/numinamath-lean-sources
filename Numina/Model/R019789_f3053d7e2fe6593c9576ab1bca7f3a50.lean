import Mathlib

theorem algebra_298560 (a b c : ℕ) (ha : 0 < a) (hc : 1 ≤ c)
    (hroots : ∃ x y, x ≠ y ∧ x > 0 ∧ y > 0 ∧ x < 1 ∧ y < 1 ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0)
    (hsum : a + b + c ≥ 1) :
    a ≥ 5 := by 
  rcases hroots with ⟨x, y, hxy, hx1, hy1, hx2, hy2, heq1, heq2⟩
  have h1 : x < 1 := by linarith
  have h2 : x > 0 := by linarith
  have h3 : x = 0 := by linarith
  omega