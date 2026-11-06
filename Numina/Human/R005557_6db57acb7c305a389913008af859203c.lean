import Mathlib

/-
Problem :
Proves the number of ordered triples (a, b, c) of distinct integers between -31 and 31 such that a + b + c > 0 is 19615 * 6.
-/
theorem combinatorics_608849 :
    {(a, b, c) : ℤ × ℤ × ℤ | a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ -31 ≤ a ∧ a ≤ 31 ∧ -31 ≤ b ∧ b ≤ 31 ∧ -31 ≤ c ∧ c ≤ 31 ∧ a + b + c > 0}.ncard = 19615 * 6 := by 
    
  -- Rewrite the set in terms of Finset.filter for cardinality calculation
  have h1 : {(a, b, c) : ℤ × ℤ × ℤ | a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ -31 ≤ a ∧ a ≤ 31 ∧ -31 ≤ b ∧ b ≤ 31 ∧ -31 ≤ c ∧ c ≤ 31 ∧ a + b + c > 0} = Finset.filter (fun s : ℤ × ℤ × ℤ => 

    let (a, b, c) := s

    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ -31 ≤ a ∧ a ≤ 31 ∧ -31 ≤ b ∧ b ≤ 31 ∧ -31 ≤ c ∧ c ≤ 31 ∧ a + b + c > 0
    
    ) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by 

    ext ⟨a, b, c⟩

    simp

    omega

  rw [h1]

  -- Convert set cardinality to Finset cardinality
  rw [Set.ncard_coe_Finset]

  -- Automatically compute the cardinality using native decision procedure

  native_decide  
