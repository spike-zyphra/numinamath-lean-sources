import Mathlib

theorem algebra_312829 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hroots : ∃ x y, x ≠ y ∧ |x| < 1 / 3 ∧ |y| < 1 / 3 ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0) :
    a + b + c ≥ 25 := by
  rcases hroots with ⟨x, y, hxy, hx, hy, heq1, heq2⟩
  have h1 : x = 0 := by
    cases' abs_lt.mp hx with h2 h3
    omega
  have h2 : y = 0 := by
    cases' abs_lt.mp hy with h4 h5
    omega
  have h3 : x = y := by 
    omega
  exfalso 
  exact hxy (by omega)