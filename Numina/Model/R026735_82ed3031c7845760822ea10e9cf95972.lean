import Mathlib

theorem number_theory_123183 (p : ℕ) (hp : Nat.Prime p)
    (h : ∃ n, n > 0 ∧ 2 * p = n ^ 2 + (n + 1) ^ 2 + (n + 2) ^ 2 + (n + 3) ^ 2) :
    36 ∣ p - 7 := by
  rcases h with ⟨n, hn_pos, heq⟩
  have eq1 : 2 * p = 4 * n ^ 2 + 12 * n + 14 := by 
    nlinarith [heq]
  have eq2 : p = 2 * n ^ 2 + 6 * n + 7 := by
    linarith
  have h4 : n % 3 = 0 := by
    by_contra h4
    have h5 : n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h5 with (h5 | h5)
    · -- n ≡ 1 (mod 3)
      have h6 : p % 3 = 0 := by 
        simp [eq2, Nat.add_mod, Nat.mul_mod, pow_two, h5, Nat.pow_mod]
      have h6a : p ≠ 3 := by 
        nlinarith [sq_pos_of_pos hn_pos, show n ≥ 1 from by omega]
      have h7 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals 
          omega
      contradiction
    · -- n ≡ 2 (mod 3)
      have h6 : p % 3 = 0 := by
        simp [eq2, Nat.add_mod, Nat.mul_mod, pow_two, h5, Nat.pow_mod]
      have h6a : p ≠ 3 := by 
        nlinarith [sq_pos_of_pos hn_pos, show n ≥ 1 from by omega]
      have h7 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals 
          omega
      contradiction
  have hn1 : ∃ k, n = 3 * k := by 
    refine ⟨n / 3, by omega⟩
  rcases hn1 with ⟨k, hkn⟩
  have hk1 : k > 0 := by 
    nlinarith [hkn, hn_pos]
  have eq3 : p = 2 * (3 * k) ^ 2 + 6 * (3 * k) + 7 := by 
    rw [hkn] at eq2
    all_goals 
      linarith
  have eq4 : p = 18 * k ^ 2 + 18 * k + 7 := by 
    nlinarith [eq3]
  have eq5 : p - 7 = 18 * k ^ 2 + 18 * k := by 
    omega
  have eq6 : p - 7 = 18 * (k ^ 2 + k) := by 
    nlinarith [eq5]
  have h5 : k ^ 2 + k = k * (k + 1) := by 
    ring
  have h8 : (k ^ 2 + k) % 2 = 0 := by 
    have : k % 2 = 0 ∨ k % 2 = 1 := by 
      omega
    rcases this with (h9 | h9)
    · -- k is even
      simp [Nat.add_mod, Nat.mul_mod, h9, pow_two, Nat.pow_mod]
    · -- k is odd
      simp [Nat.add_mod, Nat.mul_mod, h9, pow_two, Nat.pow_mod]
  have h9 : ∃ m, k ^ 2 + k = 2 * m := by 
    refine ⟨(k ^ 2 + k) / 2, by omega⟩
  rcases h9 with ⟨m, hm⟩
  have eq7 : p - 7 = 36 * m := by 
    nlinarith [eq6, hm]
  exact ⟨m, by linarith [eq7]⟩