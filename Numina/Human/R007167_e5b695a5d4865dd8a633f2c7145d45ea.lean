import Mathlib

/-
Show that if \( a, b, c, \) and \( d \) are integers with \( a \) and \( c \) nonzero such that \( a \mid b \) and \( c \mid d \), then \( ac \mid bd \).
-/
theorem number_theory_4714 (a b c d : ℤ) (hac : a ≠ 0 ∧ c ≠ 0) (hab : a ∣ b) (hcd : c ∣ d) : a * c ∣ b * d := by
  -- This can be proved directly using `mul_dvd_mul`
  apply mul_dvd_mul hab hcd
