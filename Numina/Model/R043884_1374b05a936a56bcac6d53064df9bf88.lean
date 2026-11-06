import Mathlib


open Nat


theorem algebra_608187 (a : ℕ → ℕ) (h0 : a 0 = 7) (h1 : ∀ n : ℕ, a (n + 1) = 7 ^ a n) :
a 2006 ≡ 43 [ZMOD 100] := by

  have h2 : ∀ (n : ℕ), a (n + 1) ≡ 43 [MOD 100] := by
    intro n
    induction n with
    | zero =>
      have h20 : a 1 = 7 ^ a 0 := h1 0
      rw [h20, h0]
      norm_num [Nat.ModEq]
    | succ n ih =>
      have h21 : a (n + 2) = 7 ^ a (n + 1) := by
        specialize h1 (n + 1)
        simpa using h1
      have h3 : a (n + 1) % 4 = 3 := by
        have h4 : a (n + 1) % 100 = 43 := by
          have h13 : a (n + 1) ≡ 43 [MOD 100] := ih
          simp [Nat.ModEq] at h13 ⊢
          omega
        omega
      have h10 : (7 ^ a (n + 1)) % 100 = 43 := by
        have h11 : a (n + 1) % 4 = 3 := h3
        have h12 : ∀ k : ℕ, (7 ^ (4 * k + 3)) % 100 = 43 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals
              omega
        have h13 : ∃ k : ℕ, a (n + 1) = 4 * k + 3 := by
          refine' ⟨(a (n + 1) - 3) / 4, by omega⟩
        rcases h13 with ⟨k, hk⟩
        rw [hk] 
        apply h12 k
      rw [h21]
      simp [Nat.ModEq] at *
      omega

  have h3 : a 2006 % 100 = 43 := by
    have h4 : a 2006 ≡ 43 [MOD 100] := h2 2005
    simp [Nat.ModEq] at h4 ⊢
    omega

  norm_num [Int.ModEq] at *
  omega