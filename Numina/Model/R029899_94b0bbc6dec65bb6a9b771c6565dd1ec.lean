import Mathlib

theorem number_theory_74692 {n : ℕ} (hn : ∃ a b, n = a * b ∧ a > 1 ∧ b > 1) :
    ∃ x y z, n = x * y + x * z + y * z + 1 ∧ x > 0 ∧ y > 0 ∧ z > 0 := by
  rcases hn with ⟨a, b, h_eq, ha, hb⟩
  use a - 1, b - 1, 1
  have ha1 : a ≥ 2 := by omega
  have hb1 : b ≥ 2 := by omega
  constructor
  · -- First construct the equation
    -- Show n = (a - 1) * (b - 1) + (a - 1) * 1 + (b - 1) * 1 + 1
    rw [h_eq]
    have h1 : a ≥ 2 := by omega
    have h2 : b ≥ 2 := by omega
    cases a with
    | zero => linarith
    | succ a' =>
      cases b with
      | zero => linarith
      | succ b' =>
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at *
        <;> ring_nf
        <;> omega
  constructor
  · -- Show x > 0
    omega
  constructor
  · -- Show y > 0
    omega
  · -- Show z > 0
    norm_num