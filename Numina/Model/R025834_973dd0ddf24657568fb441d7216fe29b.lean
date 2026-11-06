import Mathlib

theorem number_theory_600160 :
    IsLeast {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ x = n / (Nat.digits 10 n).sum} (199 / 19) := by
  constructor
  · -- Show 199/19 is in the set
    use 199
    norm_num
    all_goals norm_num
  · -- Show 199/19 is the least element in the set
    intro x hx
    rcases hx with ⟨n, hn, h_eq⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [h_eq] at h ⊢
    <;> norm_num at h ⊢
    <;> all_goals
      try linarith