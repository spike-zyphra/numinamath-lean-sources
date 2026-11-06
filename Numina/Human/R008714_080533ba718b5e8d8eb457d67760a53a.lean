import Mathlib

/-- If $\( a, b, \)$ and $\( c \)$ are integers such that $\( a \)$ divides $\( b \)$and $\( b \)$ divides $\( c \)$, then $\( a \)$ also divides $\( c \)$.-/
theorem number_theory_4627
(a b c : ℤ)
(h₀ : a ∣ b)
(h₁ : b ∣ c) :
-- use the transitivity of divisibility。
a ∣ c := h₀.trans h₁
