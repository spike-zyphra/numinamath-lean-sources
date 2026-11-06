import Mathlib

theorem number_theory_135585 (n : ℕ) : 5 ∣ 7^2018 + 9^(2020 * n) := by
  have h1 : 7 ^ 2018 % 5 = 4 := by
    norm_num
  have h21 : ∀ (n : ℕ), 9 ^ (2020 * n) % 5 = 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h3 : 9 ^ (2020 * (n + 1 : ℕ)) = (9 ^ (2020 * n)) * (9 ^ 2020 : ℕ) := by
        ring_nf
      rw [h3]
      rw [Nat.mul_mod]
      rw [ih]
      norm_num
  have h2 : 9 ^ (2020 * n) % 5 = 1 := h21 n
  have h3 : (7 ^ 2018 + 9 ^ (2020 * n)) % 5 = 0 := by
    omega 
  omega