import Mathlib

theorem number_theory_246162 :
    IsGreatest {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 10 99 ∧ x = n / (Nat.digits 10 n).sum} 10 := by
  constructor
  · -- Show 10 is in the set
    use 90
    constructor
    · -- Show 90 is in the range [10, 99]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 90 divided by the sum of its digits is 10
      norm_num
  · -- Show no greater element is in the set
    intro x hx
    rcases hx with ⟨n, hn, hx⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    interval_cases n <;> norm_num [hx] <;> native_decide