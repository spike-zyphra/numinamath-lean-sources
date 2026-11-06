import Mathlib

theorem number_theory_225319 :
    IsGreatest {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ x = n / (Nat.digits 10 n).sum} 100 := by
  constructor
  · -- We will show 100 is in the set by choosing n = 100
    use 100
    constructor
    · -- Show 100 ∈ [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 100 equals the ratio
      norm_num
  · -- Now we prove it is greatest
    intro x hx
    rcases hx with ⟨n, hn, h_eq⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    rw [h_eq] at *
    by_contra h
    push_neg at h
    have h5 : (n : ℝ) / (Nat.digits 10 n).sum > (100 : ℝ) := by linarith
    have h6 : (Nat.digits 10 n).sum > 0 := by
      interval_cases n <;> norm_num
    have h7 : (n : ℝ) > (100 * ((Nat.digits 10 n).sum : ℝ)) := by
      have h8 : ((Nat.digits 10 n).sum : ℝ) > (0 : ℝ) := by
        exact_mod_cast h6
      apply (lt_div_iff₀ h8).mp at h5
      linarith
    have h8 : n > 100 * ((Nat.digits 10 n).sum : ℕ) := by
      by_contra h
      push_neg at h
      have h13 : (n : ℝ) ≤ (100 * ((Nat.digits 10 n).sum : ℝ)) := by
        exact_mod_cast h
      linarith
    interval_cases n <;> norm_num at h8 h7 <;> omega