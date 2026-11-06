import Mathlib

theorem algebra_276102 (a : ℕ → ℤ) (ha : a 0 > 0) (h : a 1 > a 0)
    (h' : ∀ n, a (n + 2) = 3 * a (n + 1) - 2 * a n) :
    a 100 > 2 ^ 99 := by
  have a100 : a 100 = (a 1 - a 0) * 2 ^ 100 + (2 * a 0 - a 1) := by
    have h1 : ∀ (n : ℕ), a n = (a 1 - a 0) * 2 ^ n + (2 * a 0 - a 1) := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        simp
        <;> linarith
      | succ n =>
        cases n with
        | zero =>
          simp
          <;> linarith
        | succ n =>
          have h2 := ih (n) (by linarith)
          have h3 := ih (n + 1) (by linarith)
          simp [h', h2, h3] at *
          ring
    specialize h1 100
    simpa using h1
  rw [a100]
  have h1 : a 1 - a 0 > 0 := by linarith
  have h3 : (a 1 - a 0) * 2 ^ 100 > 2 ^ 99 := by
    have h4 : a 1 - a 0 ≥ 1 := by omega
    have h5 : (a 1 - a 0) * 2 ^ 100 ≥ 1 * 2 ^ 100 := by
      apply mul_le_mul_of_nonneg_right
      linarith
      all_goals omega
    have h6 : 1 * 2 ^ 100 > 2 ^ 99 := by
      omega
    omega
  have h5 : (a 1 - a 0) * 2 ^ 100 + (2 * a 0 - a 1) > 2 ^ 99 := by
    nlinarith [sq_nonneg (a 1 - 2 * a 0), sq_nonneg (a 0 - 1), sq_nonneg (a 1 - 2), sq_nonneg (a 1 - a 0), h]
  linarith