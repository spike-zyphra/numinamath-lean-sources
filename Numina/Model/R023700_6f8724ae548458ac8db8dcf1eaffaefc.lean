import Mathlib

theorem number_theory_28654 :
    ∀ N : ℕ, ∃ m n : ℕ,
      m > N ∧ n > N ∧
      IsSquare (50 ^ m - 50 ^ n) ∧
      ¬∃ m n : ℕ, m > N ∧ n > N ∧ IsSquare (2020 ^ m + 2020 ^ n) := by
  intro N
  use N + 1, N + 1
  constructor
  · -- Show m > N
    omega
  constructor
  · -- Show n > N
    omega
  constructor
  · -- Show IsSquare (50 ^ (N + 1) - 50 ^ (N + 1))
    have h1 : (50 ^ (N + 1) : ℕ) - (50 ^ (N + 1) : ℕ) = 0 := by
      omega
    rw [h1]
    exact ⟨0, by norm_num⟩
  · -- Show ¬∃ m n : ℕ, m > N ∧ n > N ∧ IsSquare (2020 ^ m + 2020 ^ n)
    intro h
    rcases h with ⟨m, n, hm1, hn1, h2⟩
    rcases h2 with ⟨r, hr⟩
    have h3 : r ^ 2 = (2020 ^ m + 2020 ^ n : ℕ) := by
      linarith [hr]
    have h4 : r ^ 2 % 3 = 0 ∨ r ^ 2 % 3 = 1 := by
      have h1 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by
        omega
      rcases h1 with (h1 | h1 | h1)
      · -- If r % 3 = 0
        simp [pow_two, Nat.mul_mod, h1]
      · -- If r % 3 = 1
        simp [pow_two, Nat.mul_mod, h1]
      · -- If r % 3 = 2
        simp [pow_two, Nat.mul_mod, h1]
    have h5 : (2020 ^ m + 2020 ^ n : ℕ) % 3 = 2 := by
      have h5 : ∀ (k : ℕ), (2020 : ℕ) ^ k % 3 = 1 := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          simp [pow_succ, Nat.mul_mod] at ih ⊢
          omega
      have h6 : (2020 ^ m : ℕ) % 3 = 1 := h5 m
      have h7 : (2020 ^ n : ℕ) % 3 = 1 := h5 n
      omega
    have h8 : r ^ 2 % 3 = 2 := by
      omega
    omega