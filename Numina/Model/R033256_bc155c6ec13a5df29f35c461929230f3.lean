import Mathlib

theorem number_theory_282458 :
    ¬∃ (k : ℤ) (d : ℕ), d > 0 ∧ d < 10 ∧ k^2 % 10000 = d * 1111 := by
  rintro ⟨k, d, hk, hk2, heq⟩

  have h1 : k^2 % 16 = 0 ∨ k^2 % 16 = 1 ∨ k^2 % 16 = 4 ∨ k^2 % 16 = 9 := by
    have h2 : k % 16 = 0 ∨ k % 16 = 1 ∨ k % 16 = 2 ∨ k % 16 = 3 ∨ k % 16 = 4 ∨ k % 16 = 5 ∨ k % 16 = 6 ∨ k % 16 = 7 ∨ k % 16 = 8 ∨ k % 16 = 9 ∨ k % 16 = 10 ∨ k % 16 = 11 ∨ k % 16 = 12 ∨ k % 16 = 13 ∨ k % 16 = 14 ∨ k % 16 = 15 := by
      omega 
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
  
  have h5 : (k ^ 2) % 10000 = (d * 1111 : ℤ) := by 
    simpa using heq

  -- Derive that k^2 ≡ (d * 1111) % 16 [mod 16]
  have h6 : k^2 % 10000 % 16 = (d * 1111 : ℤ) % 16 := by
    omega
  
  -- Simplify to get k^2 ≡ (d * 1111) % 16 [mod 16]
  have h7 : k^2 % 16 = (d * 1111 : ℤ) % 16 := by 
    omega
  
  -- Derive congruence properties mod 5
  have h8 : k^2 % 5 = 0 ∨ k^2 % 5 = 1 ∨ k^2 % 5 = 4 := by 
    have h9 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by 
      omega 
    rcases h9 with (h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
  
  -- Get what k^2 ≡ mod 5 from h5 (k^2 % 10000 = d * 1111).
  have h9 : k^2 % 5 = (d * 1111 : ℤ) % 5 := by 
    omega
  
  -- Now, proceed case analysis on d
  interval_cases d <;> norm_num at h7 h1 h8 h9
  <;> try { 
    omega 
  }
  <;> try { 
    have h10 : k % 16 = 0 ∨ k % 16 = 1 ∨ k % 16 = 2 ∨ k % 16 = 3 ∨ k % 16 = 4 ∨ k % 16 = 5 ∨ k % 16 = 6 ∨ k % 16 = 7 ∨ k % 16 = 8 ∨ k % 16 = 9 ∨ k % 16 = 10 ∨ k % 16 = 11 ∨ k % 16 = 12 ∨ k % 16 = 13 ∨ k % 16 = 14 ∨ k % 16 = 15 := by 
      omega
    rcases h10 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h7 h1 
    <;> omega
  }
  <;> try { 
    have h11 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by 
      omega 
    rcases h11 with (h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h9 h8 
    <;> omega 
  }