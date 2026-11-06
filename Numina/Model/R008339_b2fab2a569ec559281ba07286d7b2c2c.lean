import Mathlib

theorem number_theory_22993 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a > b ∧ b > c) (hmod : a % 19 = 4 ∧ b % 19 = 2 ∧ c % 19 = 18) :
    (2 * a + b - c) % 19 = 11 := by
  rcases hmod with ⟨ha19, hb19, hc19⟩
  omega