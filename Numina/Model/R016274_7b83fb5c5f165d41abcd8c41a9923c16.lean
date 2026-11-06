import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_208437 (a b : ℝ) :
  (∀ x ∈ Icc (-1) 1, |2*x^2 + a*x + b| ≤ 1) ↔ a = 0 ∧ b = -1 := by
  constructor
  · -- Assume that for all x in [-1, 1], |2x^2 + a x + b| ≤ 1, prove that a = 0 and b = -1.
    intro h
    have h1 := h (-1) (by norm_num)
    have h2 := h 0 (by norm_num)
    have h3 := h 1 (by norm_num)
    have h4 := h (1 / 2) (by norm_num)
    have h5 := h (-1 / 2) (by norm_num)
    have h11 : -1 ≤ 2 * (-1: ℝ) ^2 + a * (-1) + b := by
      linarith [abs_le.mp h1]
    have h12 : 2 * (-1: ℝ) ^2 + a * (-1) + b ≤ 1 := by
      linarith [abs_le.mp h1]
    have h21 : -1 ≤ 2 * (0: ℝ) ^2 + a * (0) + b := by
      linarith [abs_le.mp h2]
    have h22 : 2 * (0: ℝ) ^2 + a * (0) + b ≤ 1 := by
      linarith [abs_le.mp h2]
    have h31 : -1 ≤ 2 * (1: ℝ) ^2 + a * (1) + b := by
      linarith [abs_le.mp h3]
    have h32 : 2 * (1: ℝ) ^2 + a * (1) + b ≤ 1 := by
      linarith [abs_le.mp h3]
    have h41 : -1 ≤ 2 * (1 / 2: ℝ) ^2 + a * (1 / 2) + b := by
      linarith [abs_le.mp h4]
    have h42 : 2 * (1 / 2: ℝ) ^2 + a * (1 / 2) + b ≤ 1 := by
      linarith [abs_le.mp h4]
    have h51 : -1 ≤ 2 * (-1 / 2: ℝ) ^2 + a * (-1 / 2) + b := by
      linarith [abs_le.mp h5]
    have h52 : 2 * (-1 / 2: ℝ) ^2 + a * (-1 / 2) + b ≤ 1 := by
      linarith [abs_le.mp h5]
    constructor
    · -- Prove a = 0
      nlinarith
    · -- Prove b = -1
      nlinarith
  · -- Assume a = 0 and b = -1, prove that for all x in [-1, 1], |2x^2 + a x + b| ≤ 1.
    rintro ⟨ha, hb⟩
    intro x hx
    have hx1 : -1 ≤ x := by
      have h : x ∈ Icc (-1) 1 := hx
      exact h.1
    have hx2 : x ≤ 1 := by
      have h : x ∈ Icc (-1) 1 := hx
      exact h.2
    have h1 : -1 ≤ 2 * x^2 + a * x + b := by
      rw [show a = (0 : ℝ) by linarith [ha], show b = (-1 : ℝ) by linarith [hb]]
      nlinarith [sq_nonneg x, sq_nonneg (x - 1), sq_nonneg (x + 1)]
    have h2 : 2 * x^2 + a * x + b ≤ 1 := by
      rw [show a = (0 : ℝ) by linarith [ha], show b = (-1 : ℝ) by linarith [hb]]
      nlinarith [sq_nonneg x, sq_nonneg (x - 1), sq_nonneg (x + 1)]
    apply abs_le.mpr
    constructor <;> linarith