import Mathlib

theorem number_theory_69875 {n : ℕ} (hn : n = 87) : Nat.ofDigits 10 ([1] ++ Nat.digits 10 n ++ [2]) = 33 * n := by 
  rw [hn]
  simp [Nat.ofDigits, Nat.digits, Nat.digitsAux]
  <;> norm_num