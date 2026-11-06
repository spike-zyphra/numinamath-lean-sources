import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_172810 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = cos x * cos x + (-sin x) * (sin x - 2 * sqrt 3 * cos x)) :
  ∀ x ∈ Icc (π/4) (π/2), f x ∈ Icc (-1) (sqrt 3) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : f x = cos x * cos x + (-sin x) * (sin x - 2 * sqrt 3 * cos x) := h₀ x
  rw [h1]
  have h5 : sin x ≥ Real.sqrt 2 / 2 := by
    have h6 : sin x ≥ Real.sqrt 2 / 2 := by
      have h7 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h8 : sin x ≥ sin (π / 4) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        all_goals
          linarith [Real.pi_pos, hx1, hx2]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have h11 : cos x ≥ 0 := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith [Real.pi_pos, hx1, hx2]
    · linarith [Real.pi_pos, hx1, hx2]
  have h13 : sin x ≤ 1 := by
    apply Real.sin_le_one
  have h14 : cos x ≤ Real.sqrt 2 / 2 := by
    have h15 : cos x ≤ cos (π / 4) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      all_goals
        linarith [Real.pi_pos, hx1, hx2]
    have h16 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    nlinarith
  have h15 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  constructor
  · -- Show that $f x \geq -1$.
    have h34 : cos x * cos x + (-sin x) * (sin x - 2 * sqrt 3 * cos x) ≥ -1 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - 1), 
        sq_nonneg (sin x - cos x), sq_nonneg (sin x - 1), 
        sq_nonneg (cos x - 0), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        mul_nonneg (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num) 
      ]
    linarith
  · -- Show that $f x \leq \sqrt 3$.
    have h35 : cos x * cos x + (-sin x) * (sin x - 2 * sqrt 3 * cos x) ≤ Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        sq_nonneg (sin x - cos x), sq_nonneg (sin x - Real.sqrt 2 / 2), 
        sq_nonneg (cos x - Real.sqrt 2 / 2), 
        sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), 
        mul_nonneg (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num) 
      ]
    linarith