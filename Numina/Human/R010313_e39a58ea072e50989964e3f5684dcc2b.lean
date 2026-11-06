import Mathlib

/-- Show that if $\( a, b, c, d, \)$ and $\( m \)$ are integers such that $\( m > 0 \)$, $\( a \equiv b \mod m \)$, and $\( c \equiv d \mod m \)$, then the following properties hold:
(i) $\( a + c \equiv b + d \mod m \)$,
(ii) $\( a - c \equiv b - d \mod m \)$,
(iii) $\( a c \equiv b d \mod m \)$.-/
theorem number_theory_4643
(a b c d m : ℤ)
(h₀ : m > 0)
(h₁ : a ≡ b [ZMOD m])
(h₂ : c ≡ d [ZMOD m]) :
a + c ≡ b + d [ZMOD m] ∧ a - c ≡ b - d [ZMOD m] ∧ a * c ≡ b * d [ZMOD m] := by
  constructor
  · exact Int.ModEq.add h₁ h₂
  · constructor
    · exact Int.ModEq.sub h₁ h₂
    · exact Int.ModEq.mul h₁ h₂
