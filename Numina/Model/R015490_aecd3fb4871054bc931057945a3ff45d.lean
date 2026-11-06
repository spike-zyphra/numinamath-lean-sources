import Mathlib

open Real Filter Function
open scoped Topology

theorem algebra_124006 {φ φ' : ℝ} (hφ : φ^2 - φ - 1 = 0) (hφ' : φ'^2 - φ' - 1 = 0)
  (hφ'' : φ ≠ φ') :
  ∃ a b : ℝ, ∀ n : ℕ, (Nat.fib n : ℝ) = a * φ^n + b * φ'^n := by
    have h1 : φ^2 = φ + 1 := by linarith
    have h2 : φ'^2 = φ' + 1 := by linarith
    use (1 / (φ - φ')), (-1 / (φ - φ'))
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [Nat.fib_zero]
      field_simp [(show φ - φ' ≠ 0 by intro h; apply hφ''; linarith)]
      <;> nlinarith
    | succ n =>
      cases n with
      | zero =>
        simp [Nat.fib_one]
        field_simp [(show φ - φ' ≠ 0 by intro h; apply hφ''; linarith)]
        <;> nlinarith [h1, h2]
      | succ n =>
        have h3 := ih (n + 1) (by linarith)
        have h4 := ih (n) (by linarith)
        simp [Nat.fib_add_two, h3, h4]
        field_simp [(show φ - φ' ≠ 0 by intro h; apply hφ''; linarith)]
        <;> ring_nf
        <;> simp [pow_two, pow_succ, h1, h2]
        <;> ring