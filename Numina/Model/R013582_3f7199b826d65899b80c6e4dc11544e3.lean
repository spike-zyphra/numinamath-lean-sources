import Mathlib

theorem number_theory_119732 (a : ℕ) (ha : 2 ≤ a) :
    ∃ b ∈ Set.Icc 1 a, ∃ x : ℕ, x > 0 ∧ ∃ y : ℕ, y > 0 ∧
      y ∈ {y | ∃ x : ℕ, x > 0 ∧ y = a ^ x} ∧
      y ∈ {y | ∃ x : ℕ, x > 0 ∧ y = (a + 1) * x + b} := by
  use 1
  constructor
  · -- Show that 1 is in [1, a]
    exact ⟨by linarith, by linarith⟩
  use a - 1
  have ha1 : a - 1 > 0 := by
    omega
  constructor
  · -- Show that x > 0
    omega
  use a ^ 2
  constructor
  · -- Show that y > 0
    have h2 : a ^ 2 > 0 := by
      have h1 : a > 0 := by linarith
      nlinarith
    linarith
  constructor
  · -- Show membership in A
    use 2
    constructor
    · -- Show 2 > 0
      omega
    · -- Show y = a ^ 2
      all_goals
      norm_num
  · -- Show membership in B
    use a - 1
    constructor
    · -- Show x > 0
      omega
    · -- Show y = (a + 1) * x + 1
      cases a with
      | zero => linarith -- a ≥ 2
      | succ a =>
        cases a with
        | zero => nlinarith -- a ≥ 2
        | succ a => 
          simp [Nat.pow_two, mul_add, mul_sub, add_mul, sub_eq_add_neg, mul_assoc]
          all_goals
          ring_nf
          <;> omega