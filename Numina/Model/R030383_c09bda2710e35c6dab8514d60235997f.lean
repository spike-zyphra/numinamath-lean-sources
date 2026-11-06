import Mathlib

theorem algebra_256133 (a d : ℤ) (h : d ≠ 0) (h' : ∀ n, a + d * n > 0)
    (h'' : ∀ m n, a + d * m = a + d * n → m = n) :
    ∃ b c, c ≠ 0 ∧ ∀ n, b + c * n > 0 ∧
      (∀ m n, b + c * m = b + c * n → m = n) := by
  use 1
  use 1
  constructor
  · -- Show that c ≠ 0
    norm_num
  · -- Show that ∀ n, b + c * n > 0 ∧ (∀ m n, b + c * m = b + c * n → m = n)
    intro n
    constructor
    · -- Show that b + c * n > 0
      norm_num
      all_goals omega
    · -- Show that ∀ m n, b + c * m = b + c * n → m = n
      intro m n h_eq
      omega