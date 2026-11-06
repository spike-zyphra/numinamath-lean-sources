import Mathlib

theorem number_theory_207989 :
    IsGreatest {x : ℝ | ∃ n, n ∈ Finset.Icc 100 999 ∧ x = n / (Nat.digits 10 n).sum} (100) := by
  constructor
  · -- Show that 100 is in the set
    use 100
    constructor
    · -- Show that 100 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that the ratio is 100
      norm_num
  · -- Now show that for any x in the set, x ≤ 100
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    interval_cases n <;> norm_num -- Lean will compute the digit sum and verify the inequality
    <;> all_goals norm_num