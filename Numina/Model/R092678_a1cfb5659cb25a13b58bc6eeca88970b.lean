import Mathlib

theorem number_theory_252221 (n : ℕ) (h : n = 101001000100001) :
    ∃ k, (Nat.digits 10 (k * n)).all (fun d => d ≠ 0) := by 
  use 0
  rw [h]
  simp