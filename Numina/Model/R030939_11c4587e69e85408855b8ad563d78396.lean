import Mathlib

theorem number_theory_160878 (n : ℕ) (hn : n ≥ 10) (z : ℕ) (hz : z = 123546789) :
    ¬ Nat.Prime (Nat.ofDigits n (Nat.digits 10 z)) := by 
  rw [hz]
  have h1 : Nat.ofDigits n (Nat.digits 10 (123546789 : ℕ)) = 1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9 := by
    simp [Nat.ofDigits, Nat.digits, Nat.digitsAux]
    <;> ring_nf <;> omega
  rw [h1]
  intro h
  have h3 : (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) % 3 = 0 := by
    have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h5 with (h5 | h5 | h5)
    ·
      simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h5]
    ·
      simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h5]
      <;> omega
    ·
      simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h5]
      <;> omega
  have h4 : Nat.Prime (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) := h
  have h5 : (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) % 3 = 0 := h3
  have h6 : (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) > 3 := by
    have h9 : n ≥ 10 := hn
    have h10 : (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) > 3 := by
      have h2 : n ≥ 10 := h9
      have h3 : n ^ 8 ≥ 10 ^ 8 := by apply Nat.pow_le_pow_of_le_left h2 8
      have h4 : 1 * n ^ 8 ≥ 1 * 10 ^ 8 := by
        apply Nat.mul_le_mul
        norm_num
        linarith
      omega
    linarith
  have h7 : ¬ Nat.Prime (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) := by
    apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (1 * n ^ 8 + 2 * n ^ 7 + 3 * n ^ 6 + 5 * n ^ 5 + 4 * n ^ 4 + 6 * n ^ 3 + 7 * n ^ 2 + 8 * n + 9) by omega)
    · norm_num
    all_goals linarith
  contradiction