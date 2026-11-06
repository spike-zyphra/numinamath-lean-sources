import Mathlib

theorem number_theory_18997 :
    ∃ n : ℕ, n ∈ Finset.Icc 10000 99999 ∧ (n / 10000) % 10 = 8 ∧ ∃ k : ℕ, n = k^3 := by
  use 85184
  constructor
  · exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  constructor
  · norm_num
  · use 44
    all_goals norm_num