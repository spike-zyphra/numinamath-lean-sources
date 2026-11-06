import Mathlib

open Finset Nat Real

theorem number_theory_611288 {row: ℕ → Finset ℕ} (h0: row 0 = ∅) (h1: row 1 = {1})
(h: ∀ n: ℕ, n > 0 → ∀ x: ℕ, x ∈ row (n + 1) → ∃ a b: ℕ, a ∈ row n ∧ b ∈ row n ∧ x = a + b):
∀ n: ℕ, n > 0 → ∀ x: ℕ, x ∈ row n → x ≤ 2 ^ (n - 1) := by 
  intro n hn
  intro x hx
  have h2 : ∀ (n : ℕ), n > 0 → ∀ x ∈ row n, x ≤ 2 ^ (n - 1) := by 
    intro n hn
    induction n with
    | zero => 
      exfalso 
      linarith
    | succ k ih =>
      cases k with 
      | zero =>
        intro x hx
        rw [h1] at hx
        simp at hx ⊢
        rw [hx]
        all_goals norm_num
      | succ k =>
        intro x hx
        have h4 : x ∈ row ((k + 1) + 1) := hx
        have h3 : ∃ a b : ℕ, a ∈ row (k + 1) ∧ b ∈ row (k + 1) ∧ x = a + b := by 
          have hk1 : k + 1 > 0 := by 
            omega 
          apply h (k + 1) hk1 x h4 
        rcases h3 with ⟨a, b, ha, hb, heq⟩
        have ha1 : a ≤ 2 ^ ((k + 1) - 1) := by
          apply ih (by omega) 
          exact ha 
        have hb1 : b ≤ 2 ^ ((k + 1) - 1) := by
          apply ih (by omega) 
          exact hb 
        have heq' : x = a + b := heq 
        rw [heq']
        have h4 : a + b ≤ 2 ^ ((k + 1) - 1) + 2 ^ ((k + 1) - 1) := by 
          linarith 
        have h5 : 2 ^ ((k + 1) - 1) + 2 ^ ((k + 1) - 1) = 2 ^ ((k + 1 + 1) - 1 : ℕ) := by 
          cases k with 
          | zero => 
            all_goals norm_num 
          | succ m => 
            simp [Nat.pow_succ, Nat.mul_add, Nat.pow_add]
            all_goals ring
        have h4' : a + b ≤ 2 ^ ((k + 1 + 1) - 1 : ℕ) := by 
          linarith [h4, h5]
        simpa using h4'
  specialize h2 n hn x hx
  simpa using h2