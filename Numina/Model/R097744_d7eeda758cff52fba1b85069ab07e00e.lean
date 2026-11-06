import Mathlib

theorem number_theory_234933 {N : ℕ} (hN : N = 5 * 7 ^ 4) :
    5 ∣ N ∧ 49 ∣ N ∧ (Nat.divisors N).card = 10 := by 
  rw [hN]
  constructor
  · -- Show that 5 divides 5 * 7 ^ 4
    norm_num
  constructor
  · -- Show that 49 divides 5 * 7 ^ 4
    norm_num
  · -- Show that (Nat.divisors (5 * 7 ^ 4)).card = 10
    native_decide