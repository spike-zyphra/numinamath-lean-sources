import Mathlib

theorem number_theory_223694 (p : ℕ) (hp : p.Prime) (h : 3 < p) :
    p^2 ≡ 1 [ZMOD 12] := by
  have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h4
    push_neg at h4
    have h4' : p % 3 = 0 := by 
      omega 
    have h5 : 3 ∣ p := by 
      omega 
    have h6 : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h5 (by omega) (by omega)
    contradiction 
  have h2 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have h3 : p % 2 = 0 := by 
      omega 
    have h4 : p ≠ 2 := by 
      omega 
    have h5 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction
  have h3 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by 
    omega
  norm_num [Int.ModEq] at *
  rcases h3 with (h3 | h3 | h3 | h3)
  · 
    have h4 : (p ^ 2 : ℤ) % 12 = 1 := by
      have h5 : p % 12 = 1 := h3
      have h6 : p % 12 = 1 := h5
      have h7 : (p : ℤ) % 12 = 1 := by 
        omega 
      have h8 : (p : ℤ) ^ 2 % 12 = 1 := by 
        simp [pow_two, Int.add_emod, Int.mul_emod, h7]
      omega 
    exact h4 
  · 
    have h4 : (p ^ 2 : ℤ) % 12 = 1 := by
      have h5 : p % 12 = 5 := h3
      have h6 : p % 12 = 5 := h5
      have h7 : (p : ℤ) % 12 = 5 := by 
        omega 
      have h8 : (p : ℤ) ^ 2 % 12 = 1 := by 
        simp [pow_two, Int.add_emod, Int.mul_emod, h7]
      omega 
    exact h4 
  · 
    have h4 : (p ^ 2 : ℤ) % 12 = 1 := by
      have h5 : p % 12 = 7 := h3
      have h6 : p % 12 = 7 := h5
      have h7 : (p : ℤ) % 12 = 7 := by 
        omega 
      have h8 : (p : ℤ) ^ 2 % 12 = 1 := by 
        simp [pow_two, Int.add_emod, Int.mul_emod, h7]
      omega 
    exact h4 
  · 
    have h4 : (p ^ 2 : ℤ) % 12 = 1 := by
      have h5 : p % 12 = 11 := h3
      have h6 : p % 12 = 11 := h5
      have h7 : (p : ℤ) % 12 = 11 := by 
        omega 
      have h8 : (p : ℤ) ^ 2 % 12 = 1 := by 
        simp [pow_two, Int.add_emod, Int.mul_emod, h7]
      omega 
    exact h4