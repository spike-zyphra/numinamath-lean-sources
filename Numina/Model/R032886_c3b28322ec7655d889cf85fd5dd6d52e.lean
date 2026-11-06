import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_10192 (A B : Set ℝ) (hA : A = {x | (x - 1) / (2 * x - 1) ≤ 0})
  (hB : B = {x | x ^ 2 + 2 * x + m ≤ 0}) :
  A ⊆ B ↔ m ≤ -3 := by
  constructor
  · -- Assume A ⊆ B, prove m ≤ -3
    intro h
    have h1 : (1 : ℝ) ∈ A := by
      rw [hA]
      norm_num
    have h2 : (1 : ℝ) ∈ B := h h1
    rw [hB] at h2
    have h3 : (1 : ℝ) ^ 2 + 2 * (1 : ℝ) + m ≤ (0 : ℝ) := by
      simpa using h2
    nlinarith
  · -- Assume m ≤ -3, prove A ⊆ B
    intro hm
    intro x hx
    have h4 : x ∈ A := hx
    have h5 : (x - 1) / (2 * x - 1) ≤ (0 : ℝ) := by
      rw [hA] at h4
      simpa using h4
    rw [hB]
    by_cases h7 : (2 * x - 1) > 0
    · -- Case where denominator is positive
      have h8 : x - 1 ≤ (0 : ℝ) := by
        apply (div_nonpos_iff).mp at h5
        cases h5 with
        | inl h1 =>
          nlinarith
        | inr h2 =>
          nlinarith
      have h9 : x ≤ (1 : ℝ) := by nlinarith
      have h10 : x ^ 2 + 2 * x + m ≤ (0 : ℝ) := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - 1/2), hm]
      simpa using h10
    by_cases h8 : (2 * x - 1) < 0
    · -- Case where denominator is negative
      have h9 : x - 1 ≥ (0 : ℝ) := by
        apply (div_nonpos_iff).mp at h5
        cases h5 with
        | inl h1 =>
          nlinarith
        | inr h2 =>
          nlinarith
      nlinarith
    have h9 : 2 * x - 1 = (0 : ℝ) := by
      linarith
    have h0 : 2 * x - 1 = (0 : ℝ) := h9
    have h10 : x = (1 / 2 : ℝ) := by
      linarith
    rw [show x = (1 / 2 : ℝ) by linarith]
    have h11 : ( (1 / 2 : ℝ) ) ^ 2 + 2 * ( (1 / 2 : ℝ) ) + m ≤ (0 : ℝ) := by
      nlinarith [hm
      ]
    simpa using h11