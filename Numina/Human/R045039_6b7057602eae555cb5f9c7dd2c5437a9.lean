import Mathlib

/-
Show that if $ a $ and $ b $ are positive integers, then the least common multiple of $ a $ and $ b $, denoted as $[a, b]$, is equal to the product of $ a $ and $ b $ divided by their greatest common divisor, denoted as $(a, b)$. In mathematical terms, this can be expressed as $[a, b] = \frac{a b}{(a, b)}$.
-/
theorem number_theory_4556
    (a b : ℕ) (hab : 0 < a ∧ 0 < b) :
    Nat.lcm a b = a * b / Nat.gcd a b := by
  exact rfl
