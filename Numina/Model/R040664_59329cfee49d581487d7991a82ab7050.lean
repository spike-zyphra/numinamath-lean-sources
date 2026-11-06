import Mathlib

theorem number_theory_51058 : ∃ m n : ℕ, Nat.Coprime m n ∧ (2 + 5081081081081 : ℚ) = m / n := by 
  use 5081081081083, 1
  constructor 
  · -- Show that 5081081081083 and 1 are coprime 
    norm_num 
  · -- Show that (2 + 5081081081081) = 5081081081083 / 1
    norm_num