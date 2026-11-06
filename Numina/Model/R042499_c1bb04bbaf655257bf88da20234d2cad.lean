import Mathlib

theorem number_theory_23378 :
  ∀x:ℤ, x*9 ≡ 1 [ZMOD 100] → x ≡ 89 [ZMOD 100] := by
  intro x h
  have h1 : x * 9 % 100 = 1 := h
  have h2 : x % 100 = 89 := by
    omega
  show x ≡ 89 [ZMOD 100]
  exact h2