import Mathlib

theorem number_theory_154687 (n : ℕ) :
    9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum := by
  apply Nat.nine_dvd_iff