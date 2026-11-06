import Mathlib

theorem algebra_216592 {a : ℕ → ℕ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 4)
    (han : ∀ n ≥ 2, a n = 3 * a (n - 1) + 4 * a (n - 2)) :
    ∀ n : ℕ, ∃ m : ℕ, a n = m ^ 2 := by
  intro n 
  have h1 : ∀ n : ℕ, a n = (2 ^ n) ^ 2 := by
    intro n
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      simp [ha0]
    | succ n =>
      cases n with
      | zero =>
        simp [ha1]
      | succ n =>
        have h2 := ih (n) (by linarith)
        have h3 := ih (n + 1) (by linarith)
        have h4 : a (n + 2) = 3 * a (n + 1) + 4 * a n := by
          specialize han (n + 2) (by linarith)
          simpa using han
        simp [show n + 2 = (n + 1) + 1 by omega] at *
        rw [h4]
        rw [h2, h3]
        ring_nf
  have h2 := h1 n 
  use 2 ^ n 
  all_goals 
    simp [h2]