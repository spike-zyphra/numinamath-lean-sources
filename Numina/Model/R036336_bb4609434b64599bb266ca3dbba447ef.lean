import Mathlib

open Real
open scoped BigOperators

theorem algebra_277211 {a : ℕ → ℝ}
  (ha : ∀ k, a k = (k + 1) / ((Nat.factorial (k - 1)) + (Nat.factorial k) + (Nat.factorial (k + 1)))) :
  ∑ i in Finset.Icc 2 1991, a i + 1 / (Nat.factorial 1992) = 1 / 2 := by

  have h1 : ∀ (k : ℕ), k ≥ 1 → a k = (1 / (Nat.factorial k : ℝ)) - (1 / (Nat.factorial (k + 1) : ℝ)) := by
    intro k hk
    rw [ha]
    cases k with
    | zero => linarith
    | succ k =>
      simp [Nat.factorial]
      field_simp
      ring

  have h2 : ∀ n : ℕ, ∑ i in Finset.Icc 2 (n + 2), a i = (1 / 2 : ℝ) - (1 / (Nat.factorial (n + 3) : ℝ)) := by
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_singleton, ha]
      all_goals try norm_num [Nat.factorial]
      all_goals try linarith
    | succ n ih =>
      rw [show n + 1 + 2 = n + 3 by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      have h3 : a (n + 3) = (1 / (Nat.factorial (n + 3) : ℝ)) - (1 / (Nat.factorial (n + 4) : ℝ)) := by
        specialize h1 (n + 3) (by omega)
        simpa using h1
      rw [h3]
      field_simp [Nat.factorial]
      ring

  have h4 : ∑ i in Finset.Icc 2 1991, a i = (1 / 2 : ℝ) - (1 / (Nat.factorial 1992 : ℝ)) := by
    have h5 : ∑ i in Finset.Icc 2 (1989 + 2), a i = (1 / 2 : ℝ) - (1 / (Nat.factorial (1989 + 3) : ℝ)) := h2 1989
    have h7 : (1989 + 2 : ℕ) = 1991 := by norm_num
    rw [h7] at h5
    norm_num at h5 ⊢
    all_goals linarith

  rw [h4]
  all_goals norm_num