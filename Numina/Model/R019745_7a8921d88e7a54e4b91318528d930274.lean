import Mathlib

theorem number_theory_231406 :
    IsLeast {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).length = 2 ∧
      (Nat.digits 10 n).toFinset.card = 2 ∧ x = n / ((Nat.digits 10 n).sum : ℝ)} 1.9 := by
  constructor
  · -- Show 1.9 is in the set
    use 19
    constructor
    · -- Show 19 in [10, 99]
      simp [Finset.mem_Icc]
    constructor
    · -- Show 19 has two digits
      norm_num
    constructor
    · -- Show 19 has distinct digits
      norm_num
    · -- Show the quotient equals 1.9
      norm_num
  · -- Show that for any x in the set, 1.9 ≤ x
    intro x hx
    rcases hx with ⟨n, hn1, hn2, hn3, hx⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn10, hn19⟩
    by_contra h
    push_neg at h
    rw [hx] at h
    interval_cases n <;> norm_num at h hn2 hn3 hx <;> norm_num [hx] at h