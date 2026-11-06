import Mathlib

theorem number_theory_305220 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * 2 + b * 4 + c * 16 = 10 * 24) (h2 : a * 4 + b * 16 + c * 64 = 2 * 10) :
    a = 2 ∧ b = 2 ∧ c = 2 ∧ (a * 10 + b * 7 + c * 5) / 16 = 10 := by
  omega