import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_220284 {f : ℝ → ℝ}
  (hf : f = λ x => (sin x ^ 2 - sin x + 1) / (sin x ^ 2 + sin x + 1)) :
  IsLeast {y | ∃ x ∈ Icc 0 (2 * π), f x = y} (1 / 3) ∧
  IsGreatest {y | ∃ x ∈ Icc 0 (2 * π), f x = y} 3 ∧
  f (π / 2) = 1 / 3 ∧ f (3 * π / 2) = 3 := by
  constructor
  · -- Show that 1/3 is the least element of the set
    constructor
    · -- Prove 1/3 is attained, so in the set
      use π / 2
      constructor
      · -- Show π/2 is in [0, 2π]
        exact ⟨by linarith [pi_nonneg], by linarith [pi_nonneg]⟩
      · -- Show f(π/2) = 1/3
        rw [hf]
        have h1 : sin (π / 2 : ℝ) = 1 := sin_pi_div_two
        simp [h1]
        <;> norm_num
    · -- Prove no value less than 1/3 is in the set
      intro y hy
      rcases hy with ⟨x, hx, hx1⟩
      rw [hf] at hx1
      have hx2 : x ≥ 0 := hx.1
      have hx3 : x ≤ 2 * π := hx.2
      have h1_pos : sin x ^ 2 + sin x + 1 > 0 := by 
        nlinarith [sq_nonneg (sin x + 1 / 2), Real.sin_le_one x, Real.sin_sq_add_cos_sq x]
      have h2 : (sin x ^ 2 - sin x + 1) / (sin x ^ 2 + sin x + 1) ≥ 1 / 3 := by
        apply (le_div_iff₀ h1_pos).mpr
        nlinarith [Real.sin_le_one x, Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 1), sq_nonneg (sin x + 1)]
      linarith [h2, hx1]
  constructor
  · -- Show that 3 is the greatest element in the set
    constructor
    · -- Prove 3 is attained, so in the set
      use 3 * π / 2
      constructor
      · -- Show 3π/2 is in [0, 2π]
        exact ⟨by linarith [pi_nonneg], by linarith [pi_nonneg]⟩
      · -- Show f(3π/2) = 3
        rw [hf]
        have h2 : sin (3 * π / 2 : ℝ) = -1 := by
          have h3 : 3 * π / 2 = π + π / 2 := by ring
          rw [h3]
          rw [show sin (π + π / 2) = -sin (π / 2) by rw [sin_add, sin_pi, cos_pi]; ring]
          have h4 : sin (π / 2 : ℝ) = 1 := sin_pi_div_two
          linarith
        simp [h2]
        <;> norm_num
    · -- Prove no value greater than 3 is in the set
      intro y hy
      rcases hy with ⟨x, hx, hx1⟩
      rw [hf] at hx1
      have hx2 : x ≥ 0 := hx.1
      have hx3 : x ≤ 2 * π := hx.2
      have h1_pos : sin x ^ 2 + sin x + 1 > 0 := by 
        nlinarith [sq_nonneg (sin x + 1 / 2), Real.sin_le_one x, Real.sin_sq_add_cos_sq x]
      have h2 : (sin x ^ 2 - sin x + 1) / (sin x ^ 2 + sin x + 1) ≤ 3 := by
        apply (div_le_iff₀ h1_pos).mpr
        nlinarith [Real.sin_le_one x, Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 1), sq_nonneg (sin x + 1)]
      linarith [h2, hx1]
  constructor
  · -- Show f(π/2) = 1/3
    rw [hf]
    have h1 : sin (π / 2 : ℝ) = 1 := sin_pi_div_two
    simp [h1]
    <;> norm_num
  · -- Show f(3π/2) = 3
    rw [hf]
    have h2 : sin (3 * π / 2 : ℝ) = -1 := by
      have h3 : 3 * π / 2 = π + π / 2 := by ring
      rw [h3]
      rw [show sin (π + π / 2) = -sin (π / 2) by rw [sin_add, sin_pi, cos_pi]; ring]
      have h4 : sin (π / 2 : ℝ) = 1 := sin_pi_div_two
      linarith
    simp [h2]
    <;> norm_num