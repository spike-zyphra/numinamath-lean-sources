import Mathlib

theorem number_theory_106269 {x : ℕ} (hx : x > 0) (h : 100 / x ≤ 3 ∧ 100 / x + 7 ≤ 14 ∧ 100 / x + 14 ≤ 100 / x + 1) :
    x = 27 := by
  omega