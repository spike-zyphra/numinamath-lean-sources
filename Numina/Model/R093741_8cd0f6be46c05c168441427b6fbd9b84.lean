import Mathlib

theorem algebra_132142 {a : ℕ → ℝ} (ha0 : a 0 = 3) (ha1 : a 1 = 9)
    (han : ∀ n ≥ 2, a n = 4 * a (n - 1) - 3 * a (n - 2) - 4 * n + 2) :
    ∀ n, a n = 3 ^ n + n ^ 2 + 3 * n + 2 := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    -- Base case n = 0
    norm_num [ha0]
  | succ n =>
    cases n with
    | zero =>
      -- Base case n = 1
      norm_num [ha1]
    | succ n =>
      -- Induction step for n ≥ 2
      have h1 := ih (n + 1) (by linarith)
      have h2 := ih n (by linarith)
      specialize han (n + 2) (by linarith)
      simp [show n + 2 ≥ 2 by linarith] at han
      simp [han, h1, h2]
      ring_nf
      <;> norm_num
      <;> ring_nf <;> norm_num