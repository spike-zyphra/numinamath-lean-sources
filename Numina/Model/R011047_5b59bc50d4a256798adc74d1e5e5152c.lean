import Mathlib

theorem Algebra_611498  (a : ℕ → ℤ) (ha₀ : a 0 = 21) (ha₁ : a 1 = 35) (h: ∀ n : ℕ, 2≤ n → a (n) = 4 * a (n-1) - 4 * a (n-2) + n^2) :
  a 2006 % 100 = 36 := by

  have h1 : ∀ n, a n = (1 + 2 * n) * 2 ^ n + n ^ 2 + 8 * n + 20 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [ha₀]
      all_goals linarith
    | succ n =>
      cases n with
      | zero =>
        simp [ha₁]
        all_goals linarith
      | succ n =>
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        simp [h (n + 2) (by linarith), h2, h3]
        ring_nf
        <;> omega

  have h2 := h1 2006
  rw [h2]
  norm_num