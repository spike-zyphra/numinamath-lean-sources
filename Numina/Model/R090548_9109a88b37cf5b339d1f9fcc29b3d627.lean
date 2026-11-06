import Mathlib

theorem number_theory_116758 (n : ℕ) (hcoprime : Nat.Coprime n 10) :
    ∃ k, (Nat.digits 10 (k * n)).all (fun d => d = 1) := by 
  use 0
  simp