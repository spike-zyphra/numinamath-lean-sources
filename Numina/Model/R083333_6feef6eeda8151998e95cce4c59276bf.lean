import Mathlib

theorem number_theory_109963 (a b c d e f : ℕ) :
    11 ∣ (100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f) * 10^6 +
      (100000 * f + 10000 * e + 1000 * d + 100 * c + 10 * b + a) := by
  ring_nf
  omega