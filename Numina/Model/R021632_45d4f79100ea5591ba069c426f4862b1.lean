import Mathlib

theorem algebra_252921 {a : ℕ → ℤ} (ha : a 0 = -4) (ha1 : a 1 = -2) (ha2 : a 2 = 2)
    (h : ∀ n ≥ 3, a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + 24 * n - 6) :
    ∀ n, a n = -4 + 17 * n - 21 * n ^ 2 + 5 * n ^ 3 + n ^ 4 := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    simp [ha]
  | succ n =>
    cases n with
    | zero =>
      simp [ha1]
    | succ n =>
      cases n with
      | zero =>
        simp [ha2]
      | succ n =>
        have h1 := ih (n + 2) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        simp [h (n + 3) (by linarith)] at *
        <;> simp [h1, h2, h3] 
        <;> ring_nf 
        <;> omega