import Mathlib

/- Show that if \( a \) and \( b \) are integers, which are not both zero, and \( c \) is a nonzero integer, then the greatest common divisor of \( (c a, c b) \) is equal to the absolute value of \( c \) multiplied by the greatest common divisor of \( (a, b) \), that is, \( (c a, c b) = |c| (a, b) \). -/
theorem number_theory_4509
    {a b c : ℤ} (hab : ¬(a = 0 ∧ b = 0)) (hc : c ≠ 0) :
    (c * a).gcd (c * b) = c.natAbs * a.gcd b := by
  -- exact `Int.gcd_mul_left` in Mathlib
  apply Int.gcd_mul_left
