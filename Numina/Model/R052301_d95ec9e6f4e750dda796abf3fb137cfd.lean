import Mathlib

theorem number_theory_270396 (n : ℕ) (hn : n > 0) :
    ∃ k, (Nat.digits 10 (2^n * k)).all (fun d => d ≠ 0) := by 
  use 0
  simp