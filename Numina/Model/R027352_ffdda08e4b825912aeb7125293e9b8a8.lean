import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_265913 :
  IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a^2 + b^2 = 1 ∧ x = a^2 * (a + b^3) / (b - b^3) +
    b^2 * (b + a^3) / (a - a^3)} 3 := by
  constructor
  · -- Show that 3 is in the set
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    constructor
    · -- Show that a > 0
      positivity
    constructor
    · -- Show that b > 0
      positivity
    constructor
    · -- Show that a^2 + b^2 = 1
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith
    · -- Show that x = expression
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 3 = (Real.sqrt 2 / 2 : ℝ) * (1 / 2 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 3 = (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) ^ 2 := by ring
          _ = (Real.sqrt 2 / 2 : ℝ) * (1 / 2 : ℝ) := by rw [h1]
      have h3 : (Real.sqrt 2 / 2 : ℝ) - (Real.sqrt 2 / 2 : ℝ) ^ 3 = (Real.sqrt 2 / 4 : ℝ) := by
        rw [h2]
        linarith
      have h4 : (Real.sqrt 2 / 2 : ℝ) ^ 2 * ((Real.sqrt 2 / 2 : ℝ) + (Real.sqrt 2 / 2 : ℝ) ^ 3) = (3 / 4 : ℝ) * (Real.sqrt 2 / 2 : ℝ) := by
        have h5 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := h1
        have h6 : (Real.sqrt 2 / 2 : ℝ) ^ 3 = (Real.sqrt 2 / 2 : ℝ) * (1 / 2 : ℝ) := h2
        rw [h5, h6]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h7 : (Real.sqrt 2 / 2 : ℝ) ^ 2 * ((Real.sqrt 2 / 2 : ℝ) + (Real.sqrt 2 / 2 : ℝ) ^ 3) / ((Real.sqrt 2 / 2 : ℝ) - (Real.sqrt 2 / 2 : ℝ) ^ 3) = 3 / 2 := by
        rw [h4, h3]
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith [h7]
  · -- Show that 3 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq, hx⟩
    have eq1 : b - b ^ 3 = b * (a^2) := by
      have h3 : a^2 = 1 - b^2 := by
        nlinarith
      calc
        b - b ^ 3 = b * (1 - b^2) := by
          ring
        _ = b * (a^2) := by
          rw [h3]
    have eq2 : a - a ^ 3 = a * (b^2) := by
      have h3 : a^2 + b^2 = 1 := heq
      have h4 : b^2 = 1 - a^2 := by
        nlinarith
      calc
        a - a ^ 3 = a * (1 - a^2) := by
          ring
        _ = a * (b^2) := by
          rw [h4]
    have eq3 : a ^ 2 * (a + b ^ 3) / (b - b ^ 3) = (a + b ^ 3) / b := by
      rw [eq1]
      field_simp [(show b ≠ 0 by linarith), (show a^2 ≠ 0 by nlinarith)]
      <;> ring
    have eq4 : b ^ 2 * (b + a ^ 3) / (a - a ^ 3) = (b + a ^ 3) / a := by
      rw [eq2]
      field_simp [(show a ≠ 0 by linarith), (show b^2 ≠ 0 by nlinarith)]
      <;> ring
    have eq5 : (a + b ^ 3) / b = a / b + b^2 := by
      field_simp [(show b ≠ 0 by linarith)]
      <;> nlinarith
    have eq6 : (b + a ^ 3) / a = b / a + a^2 := by
      field_simp [(show a ≠ 0 by linarith)]
      <;> nlinarith
    have eq7 : x = (a / b + b / a + 1) := by
      rw [hx]
      rw [eq3, eq4, eq5, eq6]
      <;> nlinarith
    have h3 : a / b + b / a ≥ 2 := by
      have h4 : a / b + b / a - 2 ≥ 0 := by
        have h5 : a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by
          field_simp
          <;> ring
        have h6 : a * b > 0 := mul_pos ha hb
        rw [h5]
        positivity
      linarith
    have h4 : a / b + b / a + 1 ≥ 3 := by
      linarith [h3]
    nlinarith [eq7, h4]