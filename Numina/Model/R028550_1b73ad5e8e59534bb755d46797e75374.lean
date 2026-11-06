import Mathlib

theorem number_theory_225534 (n : ℕ) (hn : n > 0) :
    17 ∣ (2^(4*n) - 1) ∨ 17 ∣ (2^(4*n) + 1) := by
  have h1 : ∀ n : ℕ, (2 : ℕ) ^ (4 * n) % 17 = 1 ∨ (2 : ℕ) ^ (4 * n) % 17 = 16 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : (2 : ℕ) ^ (4 * (n + 1)) % 17 = ((2 : ℕ) ^ (4 * n) * (2 ^ 4)) % 17 := by
        ring_nf
      rw [h2]
      rcases ih with (h | h)
      · -- case $2^{4n} \pmod{17} = 1$
        simp [Nat.mul_mod, Nat.pow_mod, h]
      · -- case $2^{4n} \pmod{17} = 16$
        simp [Nat.mul_mod, Nat.pow_mod, h]
  have h17 : (2 : ℕ) ^ (4 * n) % 17 = 1 ∨ (2 : ℕ) ^ (4 * n) % 17 = 16 := h1 n
  rcases h17 with (h | h)
  ·
    have h1 : (17 : ℕ) ∣ (2^(4 * n) - 1) := by
      have h18 : (2 ^ (4 * n) : ℕ) % 17 = 1 := h
      have h5 : (2 ^ (4 * n) - 1 : ℕ) % 17 = 0 := by 
        omega
      exact Nat.dvd_of_mod_eq_zero h5
    left
    exact h1
  ·
    have h1 : (17 : ℕ) ∣ (2^(4 * n) + 1) := by
      have h18 : (2 ^ (4 * n) : ℕ) % 17 = 16 := h
      have h5 : (2 ^ (4 * n) + 1 : ℕ) % 17 = 0 := by 
        omega
      exact Nat.dvd_of_mod_eq_zero h5
    right
    exact h1