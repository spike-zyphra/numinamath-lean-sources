import Mathlib


theorem algebra_111631 (a : ℝ) :
    ∃ f : ℝ → ℝ, (∀ x, f (f x) = f x + x) ∧ (∀ x, f (f x - x) = f x + a * x) ↔
    a = (1 + Real.sqrt 5) / 2 := by 
  use fun x => ((1 - Real.sqrt 5) / 2) * x
  constructor
  · -- Assume both conditions hold, prove a = (1 + Real.sqrt 5)/2
    intro h
    rcases h with ⟨h1, h2⟩
    have eq1 := h2 1
    norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), mul_add, mul_sub] at eq1
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 5 - 1)]
  · -- Assume a = (1 + Real.sqrt 5)/2, prove both conditions hold
    intro ha
    rw [ha]
    constructor
    · -- Prove ∀ x, f (f x) = f x + x
      intro x
      ring_nf
      <;> simp [pow_two, mul_add, mul_assoc, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), mul_comm]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 5 - 1)]
    · -- Prove ∀ x, f (f x - x) = f x + a * x
      intro x
      ring_nf
      <;> simp [pow_two, mul_add, mul_sub, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), mul_comm]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (Real.sqrt 5 - 1)]