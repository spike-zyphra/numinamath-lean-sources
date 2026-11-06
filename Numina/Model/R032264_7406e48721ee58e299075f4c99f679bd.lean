import Mathlib

theorem algebra_319398 {a : ℕ → ℤ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = 2 * a (n - 1) + n) :
    ∀ n, a (2 * n) = 2 ^ (n + 2) - 2 * n - 3 ∧ a (2 * n + 1) = 3 * 2 ^ (n + 1) - 2 * n - 4 := by
  intro n
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero =>
    constructor
    · -- Show that a (2 * 0) = 1
      rw [show 2 * 0 = 0 by ring]
      exact ha0
    · -- Show that a (2 * 0 + 1) = 2
      rw [show 2 * 0 + 1 = 1 by ring]
      exact ha1
  | succ n =>
    have h2 := ih n (by omega)
    constructor
    · -- Show that a (2 * (n + 1)) = 2 ^ (n + 3) - 2 * (n + 1) - 3
      have eq1 : a (2 * (n + 1)) = 2 * a (2 * n) + (2 * n + 1) := by
        have eq2 : a (2 * (n + 1)) = a ((2 * n + 1) + 1) := by
          ring_nf
        rw [eq2]
        have eq3 : a ((2 * n + 1) + 1) = 2 * a ((2 * n + 1) - 1) + (2 * n + 1) := by
          apply han
          omega
        rw [eq3]
        have eq4 : (2 * n + 1 - 1 : ℕ) = 2 * n := by
          omega
        simp [eq4]
      rw [eq1, h2.1]
      simp [pow_succ, pow_zero, mul_add, mul_sub]
      <;> ring_nf <;> omega
    · -- Show the formula for a (2 * (n + 1) + 1)
      have eq3 : a (2 * (n + 1) + 1) = 2 * a (2 * n + 1) + (2 * n + 2) := by
        have eq4 : a (2 * (n + 1) + 1) = a ((2 * n + 2) + 1) := by
          ring_nf
        rw [eq4]
        have eq5 : a ((2 * n + 2) + 1) = 2 * a ((2 * n + 2) - 1) + (2 * n + 2) := by
          apply han
          omega
        rw [eq5]
        have eq6 : (2 * n + 2 - 1 : ℕ) = 2 * n + 1 := by
          omega
        simp [eq6]
      rw [eq3, h2.2]
      simp [pow_succ, pow_zero, mul_add, mul_sub]
      <;> ring_nf <;> omega