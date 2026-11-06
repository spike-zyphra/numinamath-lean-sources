import Mathlib

/-The largest prime factor of 101101101101 is a four-digit number N. Compute N -/

theorem number_theory_610644: List.maximum (Nat.primeFactorsList 101101101101) = 9901:= by
  native_decide