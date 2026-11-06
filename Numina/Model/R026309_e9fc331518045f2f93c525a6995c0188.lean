import Mathlib

theorem number_theory_267886 :
    IsLeast {x | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ x = ∑ i ∈ Finset.Icc 2 10, n % i} 3 := by 
  constructor
  · -- Show 3 is in the set.
    use 840
    constructor
    · -- Verify 840 is in the range [100, 999].
      norm_num [Finset.mem_Icc]
    · -- Verify that the sum of the remainders is 3.
      native_decide
  · -- Show that 3 is the smallest element in the set.
    intro x h
    rcases h with ⟨n, hn, hsum⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : x < 3 := by linarith
    have h2 : x = 0 ∨ x = 1 ∨ x = 2 := by
      omega
    rcases h2 with (r | r | r)
    · -- Case where x = 0
      rw [r] at hsum
      have h3 : ∑ i in Finset.Icc 2 10, n % i ≥ 3 := by
        interval_cases n <;> native_decide
      linarith
    · -- Case where x = 1
      rw [r] at hsum
      have h3 : ∑ i in Finset.Icc 2 10, n % i ≥ 3 := by
        interval_cases n <;> native_decide
      linarith
    · -- Case where x = 2
      rw [r] at hsum
      have h3 : ∑ i in Finset.Icc 2 10, n % i ≥ 3 := by
        interval_cases n <;> native_decide
      linarith