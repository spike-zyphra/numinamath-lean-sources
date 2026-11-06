import Mathlib

def isGood (n : ℕ) := n ∈ Finset.Icc 1 2015 ∧ 2016 ∣ ∑ i ∈ Finset.Icc 1 2015 \ {n}, i

theorem number_theory_167952 :
    {n | isGood n} = {1008} := by 
  ext n
  simp [isGood, Finset.mem_Icc]
  constructor 
  · -- Assume that n is good, show n = 1008
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hsum⟩
    have h1 : n ≥ 1 := hn1
    have h2 : n ≤ 2015 := hn2
    -- Compute the total sum from 1 to 2015 and express the condition on sum of the remaining numbers
    have h3 : ∑ i in Finset.Icc 1 2015 \ {n}, i = (∑ i in Finset.Icc 1 2015, i) - n := by 
      have h8 : n ≥ 1 := h1
      have h9 : n ≤ 2015 := h2
      interval_cases n <;> native_decide 
    -- The total sum from 1 to 2015 is 2015 * 1008
    have h5 : ∑ i in Finset.Icc 1 2015, i = 2015 * 1008 := by 
      native_decide 
    -- h0 : 2016 ∣ (∑ i in Finset.Icc 1 2015, i) - n 
    have h0 : 2016 ∣ ∑ i in Finset.Icc 1 2015 \ {n}, i := hsum 
    rw [h3] at h0 
    -- From the condition that (2015 * 1008 - n) divisible by 2016, we derive n = 1008
    have h7 : 2016 ∣ (2015 * 1008 - n) := by 
      rw [h5] at h0 
      omega 
    omega 
  · -- Assume n = 1008, show that n is good 
    intro h
    rw [h]
    constructor
    · -- Show 1008 is in the interval 
      all_goals native_decide 
    · -- Show the sum is divisible by 2016 
      native_decide