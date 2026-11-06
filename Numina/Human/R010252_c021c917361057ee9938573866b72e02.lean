import Mathlib

/-- Show that if $\( a, b, c, \)$ and $\( m \)$ are integers with $\( m > 0 \)$ such that $\( a \equiv b \pmod{m} \)$, then the following properties hold:
(i) $\( a + c \equiv b + c \pmod{m} \)$,
(ii) $\( a - c \equiv b - c \pmod{m} \)$,
(iii) $\( a c \equiv b c \pmod{m} \)$.-/
theorem number_theory_4640
(a b c m : ℤ) (_ : 0 < m) (h₁ : a ≡ b [ZMOD m] ) :
(a + c ≡ b + c [ZMOD m]) ∧ (a - c ≡ b - c [ZMOD m]) ∧ (a * c ≡ b * c [ZMOD m]) := by
  constructor
  · exact Int.ModEq.add h₁ rfl
  · constructor
    · exact Int.ModEq.sub h₁ rfl
    · exact Int.ModEq.mul h₁ rfl
