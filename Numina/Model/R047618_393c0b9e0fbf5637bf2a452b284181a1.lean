import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_313246 :
  IsGreatest {z : ℝ | ∃ x y, z = x - y ∧ x^2 / 4 + y^2 ≤ 1} (Real.sqrt 5) ∧
  IsLeast {z : ℝ | ∃ x y, z = x - y ∧ x^2 / 4 + y^2 ≤ 1} (-Real.sqrt 5) := by
  constructor
  · -- Show that $\sqrt{5}$ is the greatest
    constructor
    · -- Show that √5 ∈ {z : ℝ | ∃ x y, z = x - y ∧ x^2 / 4 + y^2 ≤ 1}
      use 4 * Real.sqrt 5 / 5, -Real.sqrt 5 / 5
      constructor
      · -- Show z = x - y
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    · -- Show that $\sqrt{5}$ is indeed the greatest
      intro z h
      rcases h with ⟨x, y, h_eq, h_le⟩
      have h1 : z = x - y := h_eq
      have h2 : (x) ^ 2 / 4 + y^ 2 ≤ 1 := h_le
      nlinarith [sq_nonneg ((x / 2) - 2 * y), sq_nonneg (x - 4 * y), sq_nonneg ((x / 2) * 2 - y * 4), 
                sq_nonneg (x / 2 + 2 * y), sq_nonneg (x - (-4 * y)), 
                Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
                sq_nonneg (x * Real.sqrt 5), sq_nonneg (y * Real.sqrt 5), 
                mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Show that $-\sqrt{5}$ is the least
    constructor
    · -- Show that -√5 ∈ {z : ℝ | ∃ x y, z = x - y ∧ x^2 / 4 + y^2 ≤ 1}
      use -4 * Real.sqrt 5 / 5, Real.sqrt 5 / 5
      constructor
      · -- Show z = x - y
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    · -- Show that $-\sqrt{5}$ is indeed the least
      intro z h
      rcases h with ⟨x, y, h_eq, h_le⟩
      have h1 : z = x - y := h_eq
      have h2 : (x) ^ 2 / 4 + y^ 2 ≤ 1 := h_le
      nlinarith [sq_nonneg ((x / 2) - 2 * y), sq_nonneg (x - 4 * y), sq_nonneg ((x / 2) * 2 - y * 4), 
                sq_nonneg (x / 2 + 2 * y), sq_nonneg (x - (-4 * y)), 
                Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
                sq_nonneg (x * Real.sqrt 5), sq_nonneg (y * Real.sqrt 5), 
                mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]