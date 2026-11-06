import Mathlib

/-
Show that if \( a, b, c, \) and \( m \) are integers such that \( c > 0, m > 0, \) and \( a \equiv b \pmod{m} \), then \( a c \equiv b c \pmod{m c} \).
-/
theorem number_theory_4655 (a b c m : ℤ) (hc : 0 < c) (hm : 0 < m) (h : a ≡ b [ZMOD m]) : a * c ≡ b * c [ZMOD m * c] := by
  -- If $a ≡ b (MOD m)$, then $a * c ≡ b * c (ZMOD m * c)$ for any integers a b c m.
  exact Int.ModEq.mul_right' h
