import Mathlib

theorem number_theory_218895 (n : ℤ) (h : Odd n) : n^2 ≡ 1 [ZMOD 8] := by 
  obtain ⟨k, hk⟩ := h
  have h2 : n^2 = 4 * (k^2 + k) + 1 := by 
    rw [hk]
    ring
  rw [h2]
  have h3 : (4 * (k^2 + k) + 1 : ℤ) % 8 = 1 % 8 := by 
    have h4 : (k : ℤ) % 2 = 0 ∨ (k : ℤ) % 2 = 1 := by 
      omega 
    rcases h4 with (h4 | h4)
    · -- Case where k is even
      have h5 : k % 2 = 0 := h4
      have h6 : (k : ℤ) ^ 2 % 2 = 0 := by 
        simp [pow_two, Int.mul_emod, h5]
      have h7 : ((k : ℤ) ^ 2 + k) % 2 = 0 := by 
        omega
      have h8 : (k ^ 2 + k : ℤ) % 2 = 0 := h7 
      have h9 : ∃ m : ℤ, k ^ 2 + k = 2 * m := by 
        refine ⟨(k^2 + k) / 2, by omega⟩ 
      rcases h9 with ⟨m, hm⟩ 
      have h11 : (k ^ 2 + k : ℤ) = 2 * m := hm 
      have h10 : (4 * (k^2 + k) : ℤ) % 8 = 0 := by 
        rw [h11]
        simp [Int.add_emod, Int.mul_emod]
        <;> omega 
      omega 
    · -- Case where k is odd
      have h5 : k % 2 = 1 := h4
      have h6 : (k : ℤ) ^ 2 % 2 = 1 := by 
        simp [pow_two, Int.mul_emod, h5]
      have h7 : ((k : ℤ) ^ 2 + k) % 2 = 0 := by 
        omega 
      have h8 : (k ^ 2 + k : ℤ) % 2 = 0 := h7 
      have h9 : ∃ m : ℤ, k ^ 2 + k = 2 * m := by 
        refine ⟨(k^2 + k) / 2, by omega⟩ 
      rcases h9 with ⟨m, hm⟩ 
      have h11 : (k ^ 2 + k : ℤ) = 2 * m := hm 
      have h10 : (4 * (k^2 + k) : ℤ) % 8 = 0 := by 
        rw [h11]
        simp [Int.add_emod, Int.mul_emod]
        <;> omega 
      omega 
  simp [Int.ModEq, h3]