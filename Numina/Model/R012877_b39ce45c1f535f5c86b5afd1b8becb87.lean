import Mathlib

theorem number_theory_3514 {a : ℕ} (ha : a = 2^6 * 3^3 * 6^4) :
    a.divisors.card = 88 := by
  rw [ha]
  native_decide