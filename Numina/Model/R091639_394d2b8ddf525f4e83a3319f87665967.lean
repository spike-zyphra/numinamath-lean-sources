import Mathlib

theorem number_theory_276597 :
    ∃ n, (Nat.digits 10 n).all (fun d => d ≠ 0) ∧ 5^1000 ∣ n := by
  exact ⟨0, by simp, by simp⟩