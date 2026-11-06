import Mathlib

theorem number_theory_19087 :
    IsLeast {n | 0 < n ∧ 365 ∣ 28 * n} 365 := by 
  constructor
  · -- Proving that 365 belongs to the set
    exact ⟨by norm_num, by norm_num⟩
  · -- Proving that 365 is a lower bound
    intro n hn
    have ⟨hnpos, hndiv⟩ := hn
    omega