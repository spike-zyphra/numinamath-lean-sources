import Mathlib

theorem number_theory_282533 {a b : ℕ} (hcoprime : Nat.Coprime a b) :
    (a * b).totient = a.totient * b.totient := by
  rw [Nat.totient_mul]
  all_goals
    exact hcoprime