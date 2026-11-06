import Mathlib

theorem algebra_222020 {a : ℕ → ℝ} (ha0 : a 0 = -1) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = 2 * a (n - 1) + 3 * a (n - 2) + 3 ^ n) :
    ∀ n, a n = ((4 * n - 3) * 3 ^ (n + 1) - (-1) ^ n * 7) / 16 := by
  intro n
  induction' n using Nat.strongRec with n ih
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
      have h1 := ih (n + 1) (by linarith)
      have h2 := ih (n) (by linarith)
      have h3 : a (n + 2) = 2 * a (n + 1) + 3 * a n + 3 ^ (n + 2) := by
        specialize han (n + 2) (by linarith)
        simp [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at han ⊢
        linarith
      rw [h3]
      simp [h1, h2]
      field_simp
      ring_nf