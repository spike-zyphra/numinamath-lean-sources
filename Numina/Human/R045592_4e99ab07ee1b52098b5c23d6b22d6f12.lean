import Mathlib

/-
Show that if \( a, b, \) and \( c \neq 0 \) are integers, then \( a \mid b \) if and only if \( a c \mid b c \).
-/
theorem number_theory_4736 (a b c : ℤ) (hc : c ≠ 0) : a ∣ b ↔ a * c ∣ b * c := by
  -- We need to prove this form two directions.
  constructor
  · -- First, we need to show that if $a \mid b$, then $a c \mid b c$.
    -- This can be proved directly using `Int.mul_dvd_mul_right`.
    apply Int.mul_dvd_mul_right
  · -- Second, we need to show that if $a c \mid b c$, then $a \mid b$.
    -- This can be proved directly using `Int.dvd_of_mul_dvd_mul_right` with $c \ne 0$.
    apply Int.dvd_of_mul_dvd_mul_right hc
