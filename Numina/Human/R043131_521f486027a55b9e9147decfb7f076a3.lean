import Mathlib

/-- Show that if $\( a, b, k, \)$ and $\( m \)$ are integers such that $\( k > 0 \)$ and $\( m > 0 \)$, and if $\( a \equiv b \mod m \)$, then it follows that $\( a^k \equiv b^k \mod m \)$.-/
theorem number_theory_4645
(a b m : ℤ) (_ : 0 < m) (h₂ : a ≡ b [ZMOD m]) :
  a ^ k ≡ b ^ k [ZMOD m] := by
    -- what we wantt to prove is exactly `Int.ModEq.pow`.
    exact Int.ModEq.pow k h₂
