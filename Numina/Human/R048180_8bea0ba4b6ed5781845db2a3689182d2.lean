import Mathlib

/-
Show that if \( a, b, m, \) and \( n \) are integers such that \( m > 0, n > 0, n \mid m, \) and \( a \equiv b \pmod{m} \), then \( a \equiv b \pmod{n} \).
-/
theorem number_theory_4654 (a b m n : ℤ) (ha : 0 < m) (hb : 0 < n) (hc : n ∣ m) (hd : a ≡ b [ZMOD m]) : a ≡ b [ZMOD n] := by
  -- If $n ∣ m$, and $a ≡ b (MOD m)$, then $a ≡ b (MOD n)$.
  apply Int.ModEq.of_dvd hc hd
