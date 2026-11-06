import Mathlib

theorem number_theory_6838 (a b c m : ℤ) (hm : 0 < m) : (a ≡ b [ZMOD m]) → (a * c ≡ b * c [ZMOD m]) := by
  intro h
  exact Int.ModEq.mul_right c h