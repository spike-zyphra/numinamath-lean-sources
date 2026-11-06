import Mathlib

theorem number_theory_202845 :
    IsLeast {n | n % 10 = 9 ∧ ∀ i ∈ Finset.Icc 2 10, n % i = i - 1} 2519 := by
  constructor
  · -- Prove that 2519 satisfies the conditions
    refine ⟨by norm_num, ?_⟩
    intro i hi
    fin_cases hi <;> norm_num
  · -- Prove minimality: any number in the set is ≥ 2519
    intro m hm
    rcases hm with ⟨hm10, hm⟩
    by_contra h
    push_neg at h
    have h1 : m % 2 = 1 := hm 2 (by norm_num)
    have h2 : m % 3 = 2 := hm 3 (by norm_num)
    have h3 : m % 4 = 3 := hm 4 (by norm_num)
    have h4 : m % 5 = 4 := hm 5 (by norm_num)
    have h5 : m % 6 = 5 := hm 6 (by norm_num)
    have h6 : m % 7 = 6 := hm 7 (by norm_num)
    have h7 : m % 8 = 7 := hm 8 (by norm_num)
    have h8 : m % 9 = 8 := hm 9 (by norm_num)
    have h9 : m % 10 = 9 := hm10
    interval_cases m <;> omega