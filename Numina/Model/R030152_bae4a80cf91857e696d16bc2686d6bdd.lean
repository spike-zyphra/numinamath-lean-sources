import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21118  :
    {x : ℝ | 0 ≤ x ∧ 0 ≤ 1 - √(2 - √x) ∧ 0 ≤ 2 - √x } = Set.Icc 1 4 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume x ∈ {x : ℝ | 0 ≤ x ∧ 0 ≤ 1 - √(2 - √x) ∧ 0 ≤ 2 - √x }
    intro h
    rcases h with ⟨hx1, h1, h2⟩
    have h4 : √x ≥ 0 := by positivity
    have h5 : √x ≤ 2 := by linarith
    have h6 : x ≤ 4 := by
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
    have h7 : √(2 - √x) ≤ 1 := by linarith
    have h8 : 2 - √x ≤ 1 := by
      have h9 : (√(2 - √x)) ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [show 0 ≤ √(2 - √x) by positivity, h7]
      have h10 : (√(2 - √x)) ^ 2 = (2 - √x : ℝ) := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith [h10, h9]
    have h11 : √x ≥ 1 := by
      nlinarith
    have h12 : x ≥ 1 := by
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), h11]
    constructor <;> linarith
  · -- Assume x ∈ [1, 4]
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Show 0 ≤ x
      linarith
    constructor
    · -- Show 0 ≤ 1 - √(2 - √x)
      have h1 : √x ≥ 1 := by
        have h2 : x ≥ 1 := by linarith
        have h3 : √x ≥ √(1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h4 : √(1 : ℝ) = (1 : ℝ) := Real.sqrt_eq_cases.2 (by norm_num)
        have h5 : √x ≥ (1 : ℝ) := by
          nlinarith [h3, h4]
        linarith
      have h6 : 2 - √x ≤ 1 := by
        nlinarith
      have h7 : √(2 - √x) ≤ (1 : ℝ) := by
        have h8 : 2 - √x ≤ (1 : ℝ) := h6
        have h9 : √(2 - √x) ≤ √(1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h10 : √(1 : ℝ) = (1 : ℝ) := Real.sqrt_eq_cases.2 (by norm_num)
        nlinarith [h10, h9]
      linarith
    · -- Show 0 ≤ 2 - √x
      have h4 : √x ≤ (2 : ℝ) := by
        have h5 : x ≤ (4 : ℝ) := by linarith
        have h6 : √x ≤ √(4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h7 : √(4 : ℝ) = (2 : ℝ) := by rw [Real.sqrt_eq_cases]; norm_num
        nlinarith [h7, h6]
      linarith