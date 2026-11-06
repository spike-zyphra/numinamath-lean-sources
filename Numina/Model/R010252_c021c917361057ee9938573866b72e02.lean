import Mathlib

theorem number_theory_4640
(a b c m : ℤ) (_ : 0 < m) (h₁ : a ≡ b [ZMOD m] ) :
(a + c ≡ b + c [ZMOD m]) ∧ (a - c ≡ b - c [ZMOD m]) ∧ (a * c ≡ b * c [ZMOD m]) := by
  constructor
  · -- Prove (i) $a+c \equiv b+c(\bmod m)$
    exact Int.ModEq.add_right c h₁
  constructor
  · -- Prove (ii) $a-c \equiv b-c(\bmod m)$
    exact Int.ModEq.sub_right c h₁
  · -- Prove (iii) $\quad a c \equiv b c(\bmod m)$
    exact Int.ModEq.mul_right c h₁