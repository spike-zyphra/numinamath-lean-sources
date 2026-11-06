import Mathlib

theorem algebra_209373 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha2 : a 2 = 1)
    (han : ∀ n > 0, a (n + 2) = 3 * a (n + 1) + 18 * a n + 2 ^ n) :
    ∀ n > 0, a n = 6 ^ n / 12 - (-3) ^ n / 5 - 2 ^ n / 20 := by
  intro n hn
  have h3 : ∀ (n : ℕ), n > 0 → a n = 6 ^ n / 12 - (-3) ^ n / 5 - 2 ^ n / 20 := by
    intro n hn
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      exfalso
      linarith
    | succ n =>
      cases n with
      | zero =>
        rw [ha1]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          rw [ha2]
          norm_num
        | succ n =>
          have eq1 := han (n + 1) (by linarith)
          have h4 := ih (n + 1) (by linarith)
          have h5 := ih (n + 2) (by linarith)
          simp [show n + 1 + 2 = n + 3 by omega] at eq1 ⊢
          simp [h4, h5] at eq1 ⊢
          ring_nf at eq1 ⊢
          <;> linarith
  specialize h3 n hn
  simpa using h3