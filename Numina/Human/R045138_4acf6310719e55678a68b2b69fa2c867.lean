import Mathlib

/- Show that if \( a, b, \) and \( c \) are integers such that \( c \) divides
  the product \( ab \), then \( c \) also divides the product of the greatest common divisor
  of \( a \) and \( c \) with the greatest common divisor of \( b \) and \( c \). -/
theorem number_theory_4515 (a b : ℤ) {c : ℤ} (hc : c ∣ a * b) : c ∣ (a.gcd c) * (b.gcd c) := by
  rw [Int.gcd_comm a c, Int.gcd_comm b c,
    Int.gcd_def, Int.gcd_def, ← Int.natAbs_dvd_natAbs]
  norm_cast
  -- Suffices to show `c | gcd(c,ab)`
  refine Nat.dvd_trans ?_ (Nat.gcd_mul_dvd_mul_gcd _ _ _)
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul] at hc
  -- Suffices to show `c | c` and `c | ab` which are exact assumptions.
  rw [Nat.dvd_gcd_iff]
  simpa
