import Mathlib

theorem number_theory_694 (n m l : ℕ) (hnm : n > 0 ∧ m > 0 ∧ l > 0)
    (hml : m = n + 6) (hopening : 50 ≤ n * 19) (hclosing : n * 19 ≤ 60 * l)
    (hlarge : l > 0) (hboxes : 25 * 60 = n * 19 + m * 19 + l * 19) :
    l = 25 ∧ n = 12 := by
  omega