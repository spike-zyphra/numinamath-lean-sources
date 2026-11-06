import Mathlib

theorem number_theory_150961 : ¬∃ n, ∃ k, n^2 = k ∧ k % 10000 = 2012 := by
  rintro ⟨n, ⟨k, hk1, hk2⟩⟩
  have h1 : k % 10000 = 2012 := hk2
  have h2 : k = n ^ 2 := by linarith [hk1]
  have h3 : n ^ 2 % 16 = 12 := by
    have h4 : n ^ 2 % 10000 = 2012 := by
      rw [show k = n ^ 2 by linarith] at h1
      omega
    omega 
  have h4 : n ^ 2 % 16 = 0 ∨ n ^ 2 % 16 = 1 ∨ n ^ 2 % 16 = 4 ∨ n ^ 2 % 16 = 9 := by
    have h5 : n % 16 = 0 ∨ n % 16 = 1 ∨ n % 16 = 2 ∨ n % 16 = 3 ∨ n % 16 = 4 ∨ n % 16 = 5 ∨ n % 16 = 6 ∨ n % 16 = 7 ∨ n % 16 = 8 ∨ n % 16 = 9 ∨ n % 16 = 10 ∨ n % 16 = 11 ∨ n % 16 = 12 ∨ n % 16 = 13 ∨ n % 16 = 14 ∨ n % 16 = 15 := by
      omega 
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;> simp [pow_two, Nat.mul_mod, h5]
  omega