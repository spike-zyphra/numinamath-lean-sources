import Mathlib

theorem algebra_296097 (a : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (2 * a - 1) * x - a - 3)
    (x₁ x₂ : ℝ) (hx₁ : f x₁ = 0) (hx₂ : f x₂ = 0)
    (h₁ : x₁ ≠ x₂) :
    x₁ ^ 3 + x₂ ^ 3 = -72 ↔ a = 2 := by

  have eq1 : x₁ ^ 2 + (2 * a - 1) * x₁ - a - 3 = 0 := by
    rw [h₀ x₁] at hx₁
    linarith
  have eq2 : x₂ ^ 2 + (2 * a - 1) * x₂ - a - 3 = 0 := by
    rw [h₀ x₂] at hx₂
    linarith

  have eq3 : x₁ + x₂ = 1 - 2 * a := by
    have h2 : x₁ - x₂ ≠ 0 := by
      intro h
      apply h₁
      linarith
    have eq4 : x₁ ^ 2 + (2 * a - 1) * x₁ - a - 3 - (x₂ ^ 2 + (2 * a - 1) * x₂ - a - 3) = 0 := by
      linarith [eq1, eq2]
    have eq5 : (x₁ - x₂) * (x₁ + x₂ + 2 * a - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq5) with h3 h4
    · -- Case x₁ - x₂ = 0
      exfalso
      apply h₁
      linarith
    · -- Case x₁ + x₂ + 2 * a - 1 = 0
      linarith

  have eq4 : x₁ * x₂ = -a - 3 := by
    have h5 : x₁ ^ 2 + x₂ ^ 2 = 2 * (a + 3) - (2 * a - 1) * (x₁ + x₂) := by
      nlinarith [eq1, eq2]
    nlinarith [sq_pos_of_ne_zero (show x₁ - x₂ ≠ 0 by
      intro h
      apply h₁
      linarith
    ), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - (1 - 2 * a))]

  constructor
  · -- Assume x₁^3 + x₂^3 = -72, then a = 2
    intro h
    have eq5 : x₁ ^ 3 + x₂ ^ 3 = (x₁ + x₂) ^ 3 - 3 * (x₁ + x₂) * (x₁ * x₂) := by
      nlinarith [sq_nonneg (x₁ - x₂)]
    rw [eq5] at h
    rw [show x₁ + x₂ = 1 - 2 * a by linarith [eq3] ] at h
    rw [show x₁ * x₂ = -a - 3 by nlinarith [eq4] ] at h

    have h2 : -8 * a ^ 3 + 6 * a ^ 2 - 21 * a + 82 = 0 := by
      nlinarith
    have h3 : (a - 2) * (-8 * a ^ 2 - 10 * a - 41) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case a - 2 = 0
      linarith
    · -- Case -8 * a ^ 2 - 10 * a - 41 = 0
      nlinarith [sq_nonneg (a + 5 / 8)]
  · -- Assume a = 2, then x₁^3 + x₂^3 = -72
    intro h
    have eq5 : x₁ ^ 3 + x₂ ^ 3 = (x₁ + x₂) ^ 3 - 3 * (x₁ + x₂) * (x₁ * x₂) := by 
      nlinarith [sq_nonneg (x₁ - x₂)]
    rw [eq5]
    rw [show x₁ + x₂ = 1 - 2 * a by linarith [eq3] ]
    rw [show x₁ * x₂ = -a - 3 by nlinarith [eq4] ]
    rw [h]
    norm_num