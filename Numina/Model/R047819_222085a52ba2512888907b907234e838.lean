import Mathlib

open Finset

theorem number_theory_257576 {p : ℕ → ℕ} (hp : ∀ n, p n = 1^n + 2^n + 3^n + 4^n) :
    {n | 0 < n ∧ ¬(4 ∣ n) ∧ 5 ∣ p n} = {n | 0 < n ∧ ¬(4 ∣ n)} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume h : n > 0 ∧ ¬(4 ∣ n) ∧ 5 ∣ pn
    rintro ⟨hn_pos, hn_nmod4, hn_div⟩
    exact ⟨hn_pos, hn_nmod4⟩
  · -- Assume h : n > 0 ∧ ¬(4 ∣ n)
    rintro ⟨hn_pos, hn_nmod4⟩
    have h1 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1)
    · -- n ≡ 1 (mod 4)
      have h2 : ∀ k : ℕ, 1 ^ (4 * k + 1) + 2 ^ (4 * k + 1) + 3 ^ (4 * k + 1) + 4 ^ (4 * k + 1) ≡ 0 [MOD 5] := by
        intro k
        induction k with
        | zero =>
          norm_num [Nat.ModEq]
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          norm_num [Nat.ModEq] at ih ⊢
          all_goals
            omega
      have h3 : n = 4 * (n / 4) + 1 := by
        omega
      have h5 : 1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n ≡ 0 [MOD 5] := by
        rw [show n = 4 * (n / 4) + 1 by omega]
        have h8 := h2 (n / 4)
        exact h8
      rw [hp n] at *
      norm_num [Nat.ModEq] at h5 ⊢
      all_goals
        omega
    · -- n ≡ 2 (mod 4)
      have h2 : ∀ k : ℕ, 1 ^ (4 * k + 2) + 2 ^ (4 * k + 2) + 3 ^ (4 * k + 2) + 4 ^ (4 * k + 2) ≡ 0 [MOD 5] := by
        intro k
        induction k with
        | zero =>
          norm_num [Nat.ModEq]
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          norm_num [Nat.ModEq] at ih ⊢
          all_goals
            omega
      have h3 : n = 4 * (n / 4) + 2 := by
        omega
      have h5 : 1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n ≡ 0 [MOD 5] := by
        rw [show n = 4 * (n / 4) + 2 by omega]
        have h8 := h2 (n / 4)
        exact h8
      rw [hp n] at *
      norm_num [Nat.ModEq] at h5 ⊢
      all_goals
        omega
    · -- n ≡ 3 (mod 4)
      have h2 : ∀ k : ℕ, 1 ^ (4 * k + 3) + 2 ^ (4 * k + 3) + 3 ^ (4 * k + 3) + 4 ^ (4 * k + 3) ≡ 0 [MOD 5] := by
        intro k
        induction k with
        | zero =>
          norm_num [Nat.ModEq]
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
          norm_num [Nat.ModEq] at ih ⊢
          all_goals
            omega
      have h3 : n = 4 * (n / 4) + 3 := by
        omega
      have h5 : 1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n ≡ 0 [MOD 5] := by
        rw [show n = 4 * (n / 4) + 3 by omega]
        have h8 := h2 (n / 4)
        exact h8
      rw [hp n] at *
      norm_num [Nat.ModEq] at h5 ⊢
      all_goals
        omega