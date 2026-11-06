import Mathlib

theorem number_theory_4878 : IsLeast {n : ℕ | 0 < n ∧ 2023 ∣ ∑ i in Finset.Icc 1 n, i} 867 := by 
  constructor
  · -- Show that 867 is in the set
    constructor
    · -- Show that 867 is positive
      norm_num
    · -- Show that 2023 divides the sum from 1 to 867
      native_decide
  · -- Show that 867 is the least
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n < 867 := by linarith
    have h2 : n ≤ 866 := by
      omega
    -- Proof that ¬(2023 ∣ sum i from 1 to n) for all n ≤ 866
    have h3 : ¬ (2023 ∣ ∑ i in Finset.Icc 1 n, i) := by
      interval_cases n <;> native_decide 
    exact h3 hn_div