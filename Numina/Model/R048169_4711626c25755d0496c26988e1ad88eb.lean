import Mathlib

theorem algebra_294210 (x y : ℕ → ℝ) (hx0 : x 0 = 0) (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 2) = 3 * x (n + 1) - 2 * x n)
    (hy : ∀ n, y n = (x n)^2 + 2^(n + 2)) :
    ∀ n > 0, ∃ m : ℤ, Odd m ∧ m^2 = y n := by

  have hx2 : ∀ n, x n = (2 : ℝ) ^ n - 1 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with
    | zero =>
      rw [hx0]
      norm_num 
    | succ n =>
      cases n with
      | zero =>
        rw [hx1]
        norm_num 
      | succ n =>
        have h1 := ih (n) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        simp [hxn n, h1, h2]
        ring_nf
  intro n hn
  have hyn : y n = (2 ^ n + 1) ^ 2 := by 
    rw [hy n, hx2 n]
    ring_nf
  use (2 ^ n + 1 : ℤ)
  constructor
  · -- Show that m is odd
    have h2 : Odd ((2 ^ n + 1 : ℤ) ) := by 
      use (2 ^ (n - 1) : ℤ)
      cases n with
      | zero => 
        linarith -- This should not happen because n > 0
      | succ n =>
        cases n with
        | zero => 
          norm_num 
        | succ n =>
          simp [pow_succ, mul_add, pow_zero] at *
          <;> ring_nf 
    exact h2
  · -- Show that m^2 = y n 
    rw [hyn]
    norm_num