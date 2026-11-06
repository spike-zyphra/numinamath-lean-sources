import Mathlib

/-
Show that if \(\bar{a}\) is an inverse of \(a\) modulo \(m\) and \(\bar{b}\) is an inverse of \(b\) modulo \(m\), then \(\bar{a} \bar{b}\) is an inverse of \(ab\) modulo \(m\).
-/
theorem number_theory_4690 {a a' b b' m : ℕ} (ha : a * a' ≡ 1 [MOD m]) (hb : b * b' ≡ 1 [MOD m]) : (a*b) * (a'*b') ≡ 1 [MOD m] := by
  -- The original proposition can be rewritten as $a * a' * (b * b') \equiv 1 * 1 \pmod m)
  rw [(show a * b * (a' * b') = a * a' * (b * b') by ring_nf), (show 1 = 1 * 1 by ring)]
  -- Because $a * a' \equiv 1 \pmod m$ and $b * b' \equiv 1 \pmod m$, we can conclude that $a * a' * (b * b') \equiv 1 * b \pmod m$.
  apply Nat.ModEq.mul ha hb
