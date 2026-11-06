import Mathlib

theorem number_theory_82548 : ∃ n, 1000 ∣ (Nat.fib n) ∧ n > 0 := by 
  exact ⟨1500, by native_decide, by norm_num⟩