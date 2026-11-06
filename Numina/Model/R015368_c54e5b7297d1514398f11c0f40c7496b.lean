import Mathlib

theorem number_theory_116323 :
    IsLeast {n | n ∈ Finset.Icc 10000 99999 ∧ 2014 ∣ n ∧ (Nat.divisors (n % 1000)).card = 16} 24168 := by
  constructor
  · -- Show 24168 is in the set
    constructor
    · -- Show 24168 is in the range [10000, 99999].
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 24168 is divisible by 2014.
      norm_num
    · -- Show that the number of divisors of 24168 % 1000 (i.e., 168) is 16.
      native_decide
  · -- Show 24168 is the least element in the set.
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    have h1 : n < 24168 := by omega
    have h2 : n % 2014 = 0 := by 
      omega 
    have h3 : n ≤ 24167 := by omega 
    have h4 : n % 2014 = 0 := h2 
    have h5 : ∃ k, n = 2014 * k := by 
      have : n % 2014 = 0 := h2 
      refine' ⟨n / 2014, by omega⟩ 
    rcases h5 with ⟨k, hk⟩ 
    have hk1 : k ≥ 5 := by 
      omega 
    have hk2 : k ≤ 11 := by 
      omega 
    interval_cases k <;> norm_num [hk] at hn3 hn1l hn1u h1 h 
    <;> try { contradiction }