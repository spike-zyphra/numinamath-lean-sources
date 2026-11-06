import Mathlib

theorem number_theory_149607 (n : ℕ) (hn : n > 0) :
    (∃ a b : ℤ , n = a^2 + b^2) ↔ (∃ c d : ℤ, 2 * n = c^2 + d^2) := by
  constructor
  · -- Assume that there exist integers a and b such that n = a^2 + b^2, prove that there exist integers c and d such that 2n = c^2 + d^2.
    rintro ⟨a, b, h⟩
    have h1 : (2 * n : ℤ) = (a + b) ^ 2 + (a - b) ^ 2 := by
      nlinarith [h]
    exact ⟨a + b, a - b, by linarith [h1]⟩
  · -- Assume that there exist integers c and d such that 2n = c^2 + d^2, prove that there exist integers a and b such that n = a^2 + b^2.
    rintro ⟨c, d, h⟩
    have h1 : (c : ℤ) % 2 = (d : ℤ) % 2 := by
      have h2 : (c ^ 2 : ℤ) % 2 = (d ^ 2 : ℤ) % 2 := by 
        omega
      have h3 : (c : ℤ) % 2 = 0 ∨ (c : ℤ) % 2 = 1 := by omega
      have h4 : (d : ℤ) % 2 = 0 ∨ (d : ℤ) % 2 = 1 := by omega
      rcases h3 with (h3 | h3)
      · -- If c is even
        have hc2 : (c ^ 2 : ℤ) % 2 = 0 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, h3]
        have hd2 : (d ^ 2 : ℤ) % 2 = 0 := by
          omega
        have h4' : (d : ℤ) % 2 = 0 := by
          rcases h4 with (h4 | h4)
          · 
            omega
          · 
            have : (d ^ 2 : ℤ) % 2 = 1 := by
              simp [pow_two, Int.add_emod, Int.mul_emod, h4]
            omega
        omega
      · -- If c is odd
        have hc2 : (c ^ 2 : ℤ) % 2 = 1 := by
          simp [pow_two, Int.add_emod, Int.mul_emod, h3]
        have hd2 : (d ^ 2 : ℤ) % 2 = 1 := by
          omega
        have h4' : (d : ℤ) % 2 = 1 := by
          rcases h4 with (h4 | h4)
          · 
            have : (d ^ 2 : ℤ) % 2 = 0 := by
              simp [pow_two, Int.add_emod, Int.mul_emod, h4]
            omega
          · 
            omega
        omega
    have h3 : (c + d) % 2 = 0 := by 
      omega
    have h4 : (c - d) % 2 = 0 := by 
      omega
    have h5 : ∃ k : ℤ, c + d = 2 * k := by 
      refine' ⟨(c + d) / 2, by omega⟩
    rcases h5 with ⟨k, hk⟩
    have h6 : ∃ m : ℤ, c - d = 2 * m := by 
      refine' ⟨(c - d) / 2, by omega⟩
    rcases h6 with  ⟨m, hm⟩
    have h7 : (c : ℤ) = k + m := by 
      omega
    have h8 : (d : ℤ) = k - m := by 
      omega
    have h9 : (2 * n : ℤ) = 2 * (k ^ 2 + m ^ 2 : ℤ) := by
      rw [show (c : ℤ) = k + m by linarith, show (d : ℤ) = k - m by linarith] at h
      nlinarith
    have h10 : (n : ℤ) = k ^ 2 + m ^ 2 := by
      linarith
    exact ⟨k, m, by linarith [h10]⟩