import Mathlib

open Real Set
open scoped Real

theorem algebra_214498 (α : ℝ) :
  sin α + sin (α + 2 * π / 3) + sin (α - 2 * π / 3) = 0 ∧
  sin α ^ 2 + sin (α + 2 * π / 3) ^ 2 + sin (α - 2 * π / 3) ^ 2 = 3 / 2 ∧
  sin α ^ 3 + sin (α + 2 * π / 3) ^ 3 + sin (α - 2 * π / 3) ^ 3 =
    -3 / 4 * sin (3 * α) := by
  constructor
  · -- Proof of (1)
    have h1 : sin (α + 2 * π / 3) = sin α * cos (2 * π / 3) + cos α * sin (2 * π / 3) := by
      rw [sin_add]
    have h2 : sin (α - 2 * π / 3) = sin α * cos (2 * π / 3) - cos α * sin (2 * π / 3) := by
      rw [sin_sub]
    have h3 : cos (2 * π / 3) = -1 / 2 := by
      have h4 : cos (2 * π / 3) = -1 / 2 := by
        have h5 : 2 * π / 3 = π - π / 3 := by
          ring
        rw [h5]
        rw [cos_pi_sub]
        norm_num
      exact h4
    have h4 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h5 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
        have h6 : 2 * π / 3 = π - π / 3 := by
          ring
        rw [h6]
        rw [sin_pi_sub]
        have h7 : sin (π / 3) = Real.sqrt 3 / 2 := by
          exact sin_pi_div_three
        linarith [h7]
      exact h5
    have h1' : sin (α + 2 * π / 3) = sin α * cos (2 * π / 3) + cos α * sin (2 * π / 3) := by
      rw [sin_add]
    have h2' : sin (α - 2 * π / 3) = sin α * cos (2 * π / 3) - cos α * sin (2 * π / 3) := by
      rw [sin_sub]
    rw [h1', h2', h3, h4]
    ring_nf
    <;> simp [Real.sqrt_sq, mul_add, add_mul]
    <;> ring_nf
    <;> norm_num
  constructor
  · -- Proof of (2)
    have h1 : sin (α + 2 * π / 3) = sin α * cos (2 * π / 3) + cos α * sin (2 * π / 3) := by
      rw [sin_add]
    have h2 : sin (α - 2 * π / 3) = sin α * cos (2 * π / 3) - cos α * sin (2 * π / 3) := by
      rw [sin_sub]
    have h3 : cos (2 * π / 3) = -1 / 2 := by
      have h4 : cos (2 * π / 3) = -1 / 2 := by
        have h5 : 2 * π / 3 = π - π / 3 := by
          ring
        rw [h5]
        rw [cos_pi_sub]
        norm_num
      exact h4
    have h4 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h5 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
        have h6 : 2 * π / 3 = π - π / 3 := by
          ring
        rw [h6]
        rw [sin_pi_sub]
        have h7 : sin (π / 3) = Real.sqrt 3 / 2 := by
          exact sin_pi_div_three
        linarith [h7]
      exact h5
    have h1' : sin (α + 2 * π / 3) = sin α * cos (2 * π / 3) + cos α * sin (2 * π / 3) := by
      rw [sin_add]
    have h2' : sin (α - 2 * π / 3) = sin α * cos (2 * π / 3) - cos α * sin (2 * π / 3) := by
      rw [sin_sub]
    rw [h1', h2', h3, h4]
    have h6 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h8 : cos α ^ 2 + sin α ^ 2 = 1 := by
      linarith [h6]
    ring_nf
    <;> simp [pow_two, Real.sqrt_sq, mul_add, add_mul, mul_comm]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), h8]
  · -- Proof of (3)
    have h1 : sin (α + 2 * π / 3) = sin α * cos (2 * π / 3) + cos α * sin (2 * π / 3) := by
      rw [sin_add]
    have h2 : sin (α - 2 * π / 3) = sin α * cos (2 * π / 3) - cos α * sin (2 * π / 3) := by
      rw [sin_sub]
    have h3 : cos (2 * π / 3) = -1 / 2 := by
      have h4 : cos (2 * π / 3) = -1 / 2 := by
        have h5 : 2 * π / 3 = π - π / 3 := by
          ring
        rw [h5]
        rw [cos_pi_sub]
        norm_num
      exact h4
    have h4 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h5 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
        have h6 : 2 * π / 3 = π - π / 3 := by
          ring
        rw [h6]
        rw [sin_pi_sub]
        have h7 : sin (π / 3) = Real.sqrt 3 / 2 := by
          exact sin_pi_div_three
        linarith [h7]
      exact h5
    have h1' : sin (α + 2 * π / 3) = sin α * cos (2 * π / 3) + cos α * sin (2 * π / 3) := by
      rw [sin_add]
    have h2' : sin (α - 2 * π / 3) = sin α * cos (2 * π / 3) - cos α * sin (2 * π / 3) := by
      rw [sin_sub]
    rw [h1', h2', h3, h4]
    have h6 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h5 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by
      rw [sin_three_mul]
      all_goals ring_nf <;> simp [mul_add, add_mul]
      <;> ring_nf
      all_goals norm_num
      all_goals ring
      all_goals norm_num
    have h8 : cos α ^ 2 = 1 - sin α ^ 2 := by
      linarith [h6]
    rw [h5]
    ring_nf
    <;> simp [pow_three, mul_add, mul_sub, Real.sqrt_sq, h8]
    <;> ring_nf
    <;> norm_num [h6, h8]
    <;> ring_nf
    <;> linarith [h6, h8]