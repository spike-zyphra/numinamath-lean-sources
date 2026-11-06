import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_10602 (a : ℝ) :
  (∀ x : ℝ, |2 * x - a| + |3 * x - 2 * a| ≥ a ^ 2) ↔
  a ∈ Icc (-1 / 3) (1 / 3) := by
  constructor
  · -- Assume that inequality |2x - a| + |3x - 2a| ≥ a^2 holds for all real x, need to prove a ∈ [-1/3,1/3]
    intro h
    have h1 := h (a / 2)
    have h2 : |2 * (a / 2) - a| + |3 * (a / 2) - 2 * a| ≥ a ^ 2 := by
      simpa using h1
    have h3 : |2 * (a / 2) - a| = 0 := by
      have h4 : 2 * (a / 2) - a = 0 := by
        ring
      rw [h4]
      norm_num
    have h4 : |3 * (a / 2) - 2 * a| = |-(a / 2)| := by
      have h5 : 3 * (a / 2) - 2 * a = -(a / 2) := by
        ring
      rw [h5]
    rw [h3, h4] at h2
    have h5 := h (2 * a / 3)
    have h6 : |2 * (2 * a / 3) - a| + |3 * (2 * a / 3) - 2 * a| ≥ a ^ 2 := by
      simpa using h5
    have h7 : |2 * (2 * a / 3) - a| = |a / 3| := by
      have h8 : 2 * (2 * a / 3) - a = a / 3 := by
        ring
      rw [h8]
    have h8 : |3 * (2 * a / 3) - 2 * a| = 0 := by
      have h9 : 3 * (2 * a / 3) - 2 * a = 0 := by
        ring
      rw [h9]
      norm_num
    rw [h7, h8] at h6
    constructor
    · -- Show that -1/3 ≤ a
      cases' abs_cases (a / 3) with h8 h8 <;> 
        cases' abs_cases (-(a / 2)) with h9 h9 <;> 
          nlinarith [sq_nonneg (a + 1 / 3), sq_nonneg (a - 1 / 3)]
    · -- Show that a ≤ 1/3
      cases' abs_cases (a / 3) with h8 h8 <;> 
        cases' abs_cases (-(a / 2)) with h9 h9 <;> 
          nlinarith [sq_nonneg (a + 1 / 3), sq_nonneg (a - 1 / 3)]
  · -- Assume a ∈ [-1/3,1/3], need to prove the inequality holds for all x
    rintro (h : a ∈ Icc (-1 / 3) (1 / 3))
    rcases h with ⟨ha1, ha2⟩
    intro x
    have h1 : |2 * x - a| + |3 * x - 2 * a| ≥ a ^ 2 := by
      cases' abs_cases (2 * x - a) with h1 h1 <;> 
        cases' abs_cases (3 * x - 2 * a) with h2 h2 <;> 
          nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x - 2 * a / 3), 
            sq_nonneg (a + 1 / 3), sq_nonneg (a - 1 / 3)]
    simpa using h1