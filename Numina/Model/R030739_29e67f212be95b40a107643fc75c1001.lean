import Mathlib

open Int

theorem number_theory_269850 (n : ℤ) (h : Odd n) : 512 ∣ n^12 - n^8 - n^4 + 1 := by
  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := h
    omega
  have h2 : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
    omega
  have h3 : (n ^ 4 : ℤ) % 16 = 1 := by
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      norm_num [pow_succ, Int.add_emod, Int.mul_emod, h2] at *
  have h4 : (n ^ 8 : ℤ) % 32 = 1 := by
    have h5 : (n ^ 4 : ℤ) % 32 = 1 ∨ (n ^ 4 : ℤ) % 32 = 17 := by
      have h8 : (n ^ 4) % 16 = 1 := h3
      omega
    rcases h5 with (h5 | h5)
    · 
      have h6 : (n ^ 4 : ℤ) % 32 = 1 := h5
      have h7 : (n ^ 8 : ℤ) = (n ^ 4 : ℤ) ^ 2 := by ring
      rw [h7]
      simp [pow_two, Int.add_emod, Int.mul_emod, h6]
    · 
      have h8 : (n ^ 4 : ℤ) % 32 = 17 := h5
      have h7 : (n ^ 8 : ℤ) = (n ^ 4 : ℤ) ^ 2 := by ring
      rw [h7]
      simp [pow_two, Int.add_emod, Int.mul_emod, h8]
  have h5 : 512 ∣ n^12 - n^8 - n^4 + 1 := by
    have h8 : (n ^ 4 : ℤ) % 16 = 1 := h3
    have h10 : ∃ k : ℤ, n ^ 4 = 16 * k + 1 := by
      refine' ⟨(n ^ 4 - 1) / 16, by omega⟩
    rcases h10 with ⟨k, hk⟩
    have h11 : (n ^ 8 - 1 : ℤ) = (32 * k * (8 * k + 1)) := by
      have h11' : n ^ 8 = (n ^ 4) ^ 2 := by ring
      rw [h11', hk]
      ring_nf
    have h13 : (n ^ 4 - 1 : ℤ) = (16 * k) := by
      linarith [hk]
    have h14 : (n ^ 12 - n ^ 8 - n ^ 4 + 1 : ℤ) = (n ^ 8 - 1) * (n ^ 4 - 1) := by 
      ring
    rw [h14, h11, h13]
    have h17 : 512 ∣ (32 * k * (8 * k + 1)) * (16 * k) := by
      use k ^ 2 * (8 * k + 1)
      ring
    exact h17
  exact h5