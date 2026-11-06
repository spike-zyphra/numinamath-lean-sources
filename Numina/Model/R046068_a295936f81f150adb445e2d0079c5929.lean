import Mathlib

theorem number_theory_49177 (n : ℕ) (hn : n > 0) :
    ¬ 121 ∣ n^2 + 3 * n + 5 := by 
  rintro h
  have h2 : (n ^ 2 + 3 * n + 5) % 121 = 0 := by 
    omega
  have h3 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
    omega
  have h5_mod11 : (n ^ 2 + 3 * n + 5) % 11 = 0 := by 
    omega
  have h3' : n % 11 = 4 := by 
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h5_mod11 <;> omega
  have h4' : ∃ k : ℕ, n = 11 * k + 4 := by
    refine' ⟨n / 11, by omega⟩
  rcases h4' with ⟨k, hk⟩
  have eq1 : n ^ 2 + 3 * n + 5 = 121 * (k ^ 2 + k) + 33 := by 
    rw [show n = 11 * k + 4 by linarith [hk]]
    ring_nf 
  have eq2 : (n ^ 2 + 3 * n + 5) % 121 = 33 := by
    rw [eq1]
    simp [Nat.add_mod]
  omega