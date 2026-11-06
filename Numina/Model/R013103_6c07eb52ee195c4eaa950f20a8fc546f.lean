import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_135450 (C : ℝ) :
  (∀ α β : ℝ, α^2 + β^2 ≤ 16 → ∀ x : ℝ,
    |α * sin (2 * x) + β * cos (8 * x)| ≤ C) ↔ C ≥ 4 * sqrt 2 := by 
  constructor
  · -- Forward direction: assume inequality holds for all α, β, x, prove C ≥ 4 * sqrt 2
    intro h
    have h1 := h (2 * Real.sqrt 2) (2 * Real.sqrt 2)
    have h2 : (2 * Real.sqrt 2 : ℝ) ^ 2 + (2 * Real.sqrt 2 : ℝ) ^ 2 ≤ 16 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 := h1 h2 (Real.pi / 4)
    have h4 : sin (2 * (Real.pi / 4)) = 1 := by
      have h11 : 2 * (Real.pi / 4) = Real.pi / 2 := by 
        ring
      rw [h11]
      exact sin_pi_div_two
    have h5 : cos (8 * (Real.pi / 4)) = 1 := by
      have h14 : 8 * (Real.pi / 4) = 2 * Real.pi := by 
        ring
      rw [h14]
      have h15 : cos (2 * Real.pi) = 1 := by 
        exact cos_two_pi
      linarith [h15]
    have h6 : 2 * Real.sqrt 2 * sin (2 * (Real.pi / 4)) + 2 * Real.sqrt 2 * cos (8 * (Real.pi / 4)) = 4 * Real.sqrt 2 := by
      rw [h4, h5]
      ring_nf
      <;> norm_num
      all_goals linarith
    have h7 : |2 * Real.sqrt 2 * sin (2 * (Real.pi / 4)) + 2 * Real.sqrt 2 * cos (8 * (Real.pi / 4))| = 4 * Real.sqrt 2 := by
      rw [h6]
      all_goals norm_num [abs_of_pos, mul_pos, Real.sqrt_pos.mpr]
      <;> try { 
        positivity
      }
    have h8 : 4 * Real.sqrt 2 ≤ C := by 
      linarith [abs_nonneg (2 * Real.sqrt 2 * sin (2 * (Real.pi / 4)) + 2 * Real.sqrt 2 * cos (8 * (Real.pi / 4))), h7, h3]
    linarith [h8, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0)]
  · -- Assume C ≥ 4 * sqrt 2 and prove the inequality holds for all α, β, x
    intro h α β h1 x
    have h2 : (α * sin (2 * x) + β * cos (8 * x)) ^ 2 ≤ 32 := by
      nlinarith [sq_nonneg (α * cos (8 * x) - β * sin (2 * x)), sq_nonneg (β * sin (2 * x) - α * cos (8 * x)), sq_nonneg (α * sin (2 * x) - β * cos (8 * x)), sq_nonneg (β * cos (8 * x) - α * sin (2 * x)), sq_nonneg (α - β), sq_nonneg (α + β), sq_nonneg (sin (2 * x) - cos (8 * x)), sq_nonneg (sin (2 * x) + cos (8 * x)), Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq (8 * x), h1, Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq (8 * x), sq_nonneg (sin (2 * x) - cos (8 * x)), sq_nonneg (sin (2 * x) + cos (8 * x)), sq_nonneg (α * β), sq_nonneg ((α - β) * (α + β)), sq_nonneg (α * sin (2 * x)), sq_nonneg (β * cos (8 * x))]
    have h6 : Real.sqrt ((α * sin (2 * x) + β * cos (8 * x)) ^ 2) ≤ Real.sqrt (32 : ℝ) := Real.sqrt_le_sqrt (by linarith [h2])
    have h8 : Real.sqrt ((α * sin (2 * x) + β * cos (8 * x)) ^ 2) = |α * sin (2 * x) + β * cos (8 * x)| := by
      rw [Real.sqrt_sq_eq_abs]
    have h7' : |α * sin (2 * x) + β * cos (8 * x)| ≤ Real.sqrt (32 : ℝ) := by
      linarith [h6, h8]
    have h33 : Real.sqrt (32 : ℝ) = 4 * Real.sqrt (2 : ℝ) := by
      have h1 : Real.sqrt (32 : ℝ) = Real.sqrt (4 ^ 2 * (2 : ℝ)) := by
        ring_nf
      rw [h1]
      have h2 : Real.sqrt ((4 ^ 2) * (2 : ℝ)) = (4 : ℝ) * Real.sqrt (2 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
        have h3 : Real.sqrt ((4 : ℝ) ^ 2) = (4 : ℝ) := Real.sqrt_sq (by norm_num)
        rw [h3]
        all_goals norm_num
        all_goals positivity
      rw [h2]
      all_goals norm_num
      all_goals positivity
    have h34 : |α * sin (2 * x) + β * cos (8 * x)| ≤ 4 * Real.sqrt 2 := by 
      linarith [h7', h33]
    have h41 : 4 * Real.sqrt 2 ≤ C := by linarith [h]
    have h6' : |α * sin (2 * x) + β * cos (8 * x)| ≤ C := by
      linarith [h34, h41]
    exact h6'