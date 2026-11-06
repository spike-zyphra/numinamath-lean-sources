import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_231500 (a : ℝ) :
  (∃! x : ℝ, a * x ^ 2 + (sin x) ^ 2 = a ^ 2 - a) ↔ a = 1 := by
  constructor
  · -- Assume that the solution is unique, prove a = 1
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have hx3 := hx2 (-x) (by
      have eq1 : a * (-x) ^ 2 + (sin (-x)) ^ 2 = a * x ^ 2 + (sin x) ^ 2 := by
        have h2 : sin (-x) = -sin x := by
          rw [sin_neg]
        rw [h2]
        ring_nf
        <;> simp [mul_pow]
        <;> ring_nf
      have eq2 : a * x ^ 2 + (sin x) ^ 2 = a ^ 2 - a := by
        simpa using hx1
      linarith [eq1, eq2]
    )
    have hx4 : x = 0 := by
      have h2 : -x = x := by
        simpa using hx3
      linarith [h2]
    rw [hx4] at hx1
    have h_eq2 : a^2 - a = 0 := by
      simp [sin_zero] at hx1
      linarith
    have h_eq3 : a * (a - 1) = 0 := by
      linarith [h_eq2]
    cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
    · -- Case a = 0
      -- This case is impossible because it would imply non-trivial solutions
      have h0 : a = 0 := by
        linarith
      -- Check that, for example, π is a solution if a = 0.
      -- If a = 0, the equation becomes sin^2(y) = 0
      have h_eq6 := hx2 (Real.pi) (by
        rw [h0]
        norm_num [Real.sin_pi]
        <;> linarith
      )
      -- This would imply π = 0, which is false
      nlinarith [Real.pi_pos]
    · -- Case a - 1 = 0, so a = 1
      linarith
  · -- Backward direction: if a = 1, then there's a unique solution.
    intro ha
    rw [ha]
    use (0 : ℝ)
    constructor
    · -- Show 0 is a solution
      norm_num [Real.sin_zero]
      <;> linarith
    · -- Show if y is a solution, then y = 0
      intro y hy
      have h_eq1 : (1 : ℝ) * y ^ 2 + (sin y) ^ 2 = (1 : ℝ) ^ 2 - (1 : ℝ) := by
        simpa using hy
      have h_eq2 : y^2 + (sin y)^2 = 0 := by
        nlinarith
      have h_eq3 : y^2 ≥ 0 := by
        apply sq_nonneg
      have h_eq4 : (sin y) ^2 ≥ 0 := by
        apply sq_nonneg
      have h_eq5 : y ^ 2 = 0 := by
        nlinarith [show (sin y) ^ 2 ≤ 1 by nlinarith [Real.sin_sq_le_one y]]
      have h_eq6 : y = 0 := by
        nlinarith
      exact h_eq6