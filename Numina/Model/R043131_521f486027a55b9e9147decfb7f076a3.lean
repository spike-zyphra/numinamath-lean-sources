import Mathlib

theorem number_theory_4645
(a b m : ℤ) (_ : 0 < m) (h₂ : a ≡ b [ZMOD m]) :
  a ^ k ≡ b ^ k [ZMOD m] := by 
  exact Int.ModEq.pow k h₂