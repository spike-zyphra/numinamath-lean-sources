import Mathlib

theorem number_theory_40336 {a b : ℕ} (ha : a > 1) (hb : b > 1)
    (h : a * b > 1) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a * b = x * y + x * z + y * z + 1 := by
  use a - 1, b - 1, 1
  constructor
  · -- Show that x > 0
    have h1 : a > 1 := ha
    have hx1 : a - 1 > 0 := by omega
    exact hx1
  constructor
  · -- Show that y > 0
    have h2 : b > 1 := hb
    have hy1 : b - 1 > 0 := by omega
    exact hy1
  constructor
  · -- Show that z > 0
    norm_num
  · -- Show that a * b = x * y + x * z + y * z + 1
    cases a with
    | zero =>
      omega
    | succ a =>
      cases b with
      | zero =>
        omega
      | succ b =>
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.succ_mul, Nat.mul_succ]
        <;> ring_nf
        <;> omega