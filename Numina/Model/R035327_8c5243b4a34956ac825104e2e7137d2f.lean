import Mathlib

theorem algebra_21690 :
    IsLeast {n | n ∈ Finset.Icc 1000 9999 ∧ ∃ k, n = k * (k + 1)} 1056 := by
  constructor 
  · -- Show that 1056 is in the set.
    constructor
    · -- Show 1056 ∈ Finset.Icc 1000 9999
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show there exists k such that 1056 = k * (k + 1)
      use 32
      all_goals norm_num
  · -- Show that 1056 is minimal in the set.
    intro n hn 
    rcases hn with ⟨hn1, ⟨k, hk⟩⟩
    rw [Finset.mem_Icc] at hn1
    have h1 : k * (k + 1) ≥ 1000 := by
      nlinarith
    have h2 : k ≥ 32 := by 
      by_contra h 
      push_neg at h 
      have h4 : k ≤ 31 := by linarith 
      have h5 : k * (k + 1) < 1000 := by 
        have h4 : k ≤ 31 := by linarith 
        interval_cases k <;> omega 
      nlinarith
    have h6 : k * (k + 1) ≥ 1056 := by 
      have h7 : k ≥ 32 := h2
      nlinarith [sq_nonneg (k - 32 : ℤ), sq_nonneg (k - 33 : ℤ)]
    have hn2 : n ≥ 1056 := by 
      nlinarith [hk, h6]
    linarith