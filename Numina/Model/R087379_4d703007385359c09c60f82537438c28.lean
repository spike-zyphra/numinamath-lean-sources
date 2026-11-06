import Mathlib

theorem number_theory_7073 (a b : ℤ) (m n : ℕ) (_ : 0 < m) (hn : 0 < n)
    (h : a ≡ b [ZMOD m]) : a ^ n ≡ b ^ n [ZMOD m] := by 
  exact Int.ModEq.pow n h