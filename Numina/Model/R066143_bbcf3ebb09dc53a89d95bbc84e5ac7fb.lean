import Mathlib

theorem algebra_319956 {a : ℕ → ℤ} (ha : a 0 = 2) (ha1 : a 1 = 3)
    (han : ∀ n ≥ 2, a n = 3 * a (n - 1) - 2 * a (n - 2)) :
    ∀ n, a n = 2 ^ n + 1 := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    simp [ha]
    all_goals linarith
  | succ n =>
    cases n with
    | zero =>
      simp [ha1]
      all_goals linarith
    | succ n =>
      have h1 := han (n + 2) (by linarith)
      simp [show n + 2 ≥ 2 by linarith] at h1
      have h2 := ih (n + 1) (by linarith)
      have h3 := ih (n) (by linarith)
      simp [h1, h2, h3, pow_succ, mul_add, mul_comm, mul_assoc]
      <;> ring