import Mathlib

theorem algebra_286080 (a : ℕ → ℝ) (ha0 : a 0 = 27 / 4) (ha1 : a 1 = 49 / 4)
    (han : ∀ n ≥ 2, a n = 5 * a (n - 1) - 6 * a (n - 2) + n + 2) :
    ∀ n ≥ 0, a n = 3 * 2 ^ n + 3 ^ n + (1 / 2) * n + 11 / 4 := by
  intro n hn
  have h1 : ∀ n : ℕ, n ≥ 0 → a n = 3 * 2 ^ n + 3 ^ n + (1 / 2) * n + 11 / 4 := by
    intro n hn
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      rw [ha0]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [ha1]
        norm_num
      | succ n =>
        have h2 : (n + 2 : ℕ) ≥ 2 := by omega
        have h11 : a (n + 2) = 5 * a (n + 1) - 6 * a n + (n + 2 : ℝ) + 2 := by 
          specialize han (n + 2) (by omega)
          simp [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at han 
          linarith [han]
        have ih1 : a (n + 1) = 3 * 2 ^ (n + 1) + 3 ^ (n + 1) + (1 / 2 : ℝ) * (n + 1 : ℝ) + 11 / 4 := by
          specialize ih (n + 1) (by omega)
          simpa using ih 
        have ih2 : a n = 3 * 2 ^ n + 3 ^ n + (1 / 2 : ℝ) * (n : ℝ) + 11 / 4 := by 
          specialize ih n (by omega)
          simpa using ih
        rw [h11, ih1, ih2]
        field_simp
        ring 
  specialize h1 n hn
  assumption