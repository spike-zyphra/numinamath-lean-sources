import Mathlib

theorem algebra_195070 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 2)
    (han : ∀ n ≥ 1, a (n + 2) = 5 * a (n + 1) - 6 * a n) :
    ∀ n ≥ 1, a n = 2 ^ (n - 1) := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    linarith 
  | succ n =>
    cases n with
    | zero =>
      simp [ha1]
      <;> tauto
    | succ n =>
      cases n with
      | zero =>
        simp [ha2]
        all_goals tauto
      | succ n =>
        have h1 := ih (n + 1) (by linarith)
        have h2 := ih (n + 2) (by linarith)
        have h3 := han (n + 1) (by linarith)
        simp [show n + 1 + 2 = n + 3 by omega] at h3 ⊢
        simp [h1, h2, h3]
        ring_nf
        <;> omega