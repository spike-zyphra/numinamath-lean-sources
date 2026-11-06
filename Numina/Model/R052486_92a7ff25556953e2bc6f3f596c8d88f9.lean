import Mathlib

theorem number_theory_173325 :
    IsGreatest {x | ∃ n, n ∈ Finset.Icc 2013 2156 ∧ n % 5 = x ∧ n % 11 = x ∧ n % 13 = x} 4 := by
  constructor
  · -- Show that 4 is in the set
    use 2149
    constructor
    · -- Show that 2149 is in the range [2013, 2156]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 2149 % 5 = 4
      norm_num
    constructor
    · -- Show that 2149 % 11 = 4
      norm_num
    · -- Show that 2149 % 13 = 4
      norm_num
  · -- Show that 4 is the greatest in the set
    intro y hy
    rcases hy with ⟨n, hn1, hn2, hn3, hn4⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    have h2 : y ≤ 4 := by 
      omega
    linarith