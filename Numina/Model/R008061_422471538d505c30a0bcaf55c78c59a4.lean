import Mathlib

theorem number_theory_13269 : IsLeast {n | 0 < n ∧ n ∈ Finset.Icc 1000 9999 ∧ n % 7 = 6} 1000 := by
  constructor
  · -- Show that 1000 is in the set
    refine ⟨by norm_num, by norm_num [Finset.mem_Icc], by norm_num⟩
  · -- Show that for all n in the set, 1000 ≤ n
    intro n hn
    rcases hn with ⟨hn_pos, hn_mem, hn_mod⟩
    rw [Finset.mem_Icc] at hn_mem
    rcases hn_mem with ⟨hn1, hn2⟩
    linarith