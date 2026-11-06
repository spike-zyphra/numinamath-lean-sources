import Mathlib

theorem number_theory_4655 (a b c m : ℤ) (hc : 0 < c) (hm : 0 < m) (h : a ≡ b [ZMOD m]) : a * c ≡ b * c [ZMOD m * c] := by
  exact Int.ModEq.mul_right' h