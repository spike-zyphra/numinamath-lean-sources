import Mathlib

theorem number_theory_116072 (n : ℕ) :
    7 ∣ 4 * 15 ^ n + 4 * 134 ^ n + 34 ^ (2 * n + 1) := by
  have h1 : ∀ n : ℕ, (4 * 15 ^ n + 4 * 134 ^ n + 34 ^ (2 * n + 1) : ℕ) % 7 = 0 := by
    intro n
    have h5 : ∀ (n : ℕ), (15 ^ n) % 7 = 1 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        have : 15 ^ (n + 1) = 15 ^ n * 15 := by ring
        rw [this]
        rw [Nat.mul_mod, ih]
        all_goals norm_num
    have h6 : ∀ (n : ℕ), (134 ^ n) % 7 = 1 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        have : 134 ^ (n + 1) = 134 ^ n * 134 := by ring
        rw [this]
        rw [Nat.mul_mod, ih]
        all_goals norm_num
    have h7 : ∀ (n : ℕ), (34 ^ (2 * n + 1)) % 7 = 6 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        have : 34 ^ (2 * (n + 1) + 1) = 34 ^ (2 * n + 1) * 34 ^ 2 := by ring
        rw [this]
        rw [Nat.mul_mod, ih]
        all_goals norm_num
    have h8 : (4 * 15 ^ n + 4 * 134 ^ n + 34 ^ (2 * n + 1) : ℕ) % 7 = 0 := by
      have h9 : (4 * 15 ^ n : ℕ) % 7 = 4 := by
        have h10 : (15 ^ n) % 7 = 1 := h5 n
        norm_num [Nat.mul_mod, h10]
      have h11 : (4 * 134 ^ n : ℕ) % 7 = 4 := by
        have h12 : (134 ^ n) % 7 = 1 := h6 n
        norm_num [Nat.mul_mod, h12]
      have h13 : (34 ^ (2 * n + 1) : ℕ) % 7 = 6 := h7 n
      omega
    exact h8
  have h2 : (4 * 15 ^ n + 4 * 134 ^ n + 34 ^ (2 * n + 1) : ℕ) % 7 = 0 := h1 n
  exact Nat.dvd_of_mod_eq_zero h2