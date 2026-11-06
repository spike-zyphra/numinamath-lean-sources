import Mathlib

/-- Show that for a positive integer $\( m \)$, congruences modulo $\( m \)$ exhibit three key properties: reflexivity, symmetry, and transitivity. Specifically, these properties are defined as follows: 
(i) Reflexive property: For any integer $\( a \)$, it holds that $\( a \equiv a \mod m \)$.
(ii) Symmetric property: If two integers $\( a \)$ and $\( b \)$ satisfy $\( a \equiv b \mod m \)$, then it follows that $\( b \equiv a \mod m \)$.
(iii) Transitive property: If integers $\( a, b, \)$ and $\( c \)$ satisfy $\( a \equiv b \mod m \)$ and $\( b \equiv c \mod m \)$, then it must be true that $\( a \equiv c \mod m \)$.-/
theorem number_theory_4639
(m : ℕ) (_ : 0 < m) :
(∀ a : ℤ, a ≡ a [ZMOD m]) ∧
(∀ a b : ℤ, a ≡ b [ZMOD m] → b ≡ a [ZMOD m]) ∧
(∀ a b c : ℤ, a ≡ b [ZMOD m] → b ≡ c [ZMOD m] → a ≡ c [ZMOD m]) := by
  constructor
  · intro a; simp
  · constructor
    · intro a b hab; exact id (Int.ModEq.symm hab)
    · intro a b c hab hbc; exact hab.trans hbc
