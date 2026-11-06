import Mathlib

theorem number_theory_134766 :
    ¬∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = n - (Nat.digits 10 n).prod := by
  intro h
  rcases h with ⟨n, hn1, hn2⟩
  rw [Finset.mem_Icc] at hn1
  rcases hn1 with ⟨hn1_lower, hn1_upper⟩
  interval_cases n <;> norm_num at hn2 <;> norm_num <;> all_goals omega