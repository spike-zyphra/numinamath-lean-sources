import Mathlib

theorem algebra_302796 (a : ℕ → ℤ) (ha : ∀ n, a n = 72 * n + 63 - 2 ^ (n + 6) + (-7) ^ n) :
    ∀ n, 576 ∣ a n := by
  intro n
  have h1 : ∀ n, 576 ∣ a n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [ha]
      all_goals omega
    | succ n =>
      cases n with
      | zero =>
        simp [ha]
        all_goals omega
      | succ n =>
        have h2 := ih (n) (by linarith)
        have h3 := ih (n + 1) (by linarith)
        simp [ha] at h2 h3 ⊢
        ring_nf at h2 h3 ⊢
        omega
  specialize h1 n
  simpa using h1