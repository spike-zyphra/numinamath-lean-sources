import Mathlib

theorem algebra_199182 (K : ℤ) :
    ∃ x y : ℝ, 2 * ⌊x⌋ + y = 3 / 2 ∧ (⌊x⌋ - x) ^ 2 - 2 * ⌊y⌋ = K ↔
    ∃ M : ℤ, y = 3 / 2 - 2 * M ∧ K = 4 * M - 2 := by
  use (0 : ℝ)
  use (3 / 2 : ℝ)
  constructor
  · -- Forward direction: from the system, deduce the existence of M
    intro h
    rcases h with ⟨h1, h2⟩
    have h4 : ⌊(0 : ℝ)⌋ = (0 : ℤ) := by simp
    have h5 : ⌊(3 / 2 : ℝ)⌋ = (1 : ℤ) := by norm_num
    have h6 : (⌊ (0 : ℝ) ⌋ : ℝ) = (0 : ℝ) := by simp
    have h7 : (⌊ (3 / 2 : ℝ) ⌋ : ℝ) = (1 : ℝ) := by norm_num
    have h8 : (K : ℝ) = (-2 : ℝ) := by
      simp [h4, h5, h6, h7] at h2
      nlinarith
    have h9 : K = -2 := by
      exact_mod_cast h8
    refine ⟨0, by norm_num [h8], by omega⟩
  · -- Backward direction: from the existence of M, deduce the system
    rintro ⟨M, h4, h5⟩
    have h6 : (K : ℝ) = (4 * M - 2 : ℝ) := by
      have h7 : (K : ℝ) = (4 * M - 2 : ℝ) := by
        have h8 : K = 4 * M - 2 := by
          linarith [h5]
        exact_mod_cast h8
      linarith
    have h41 : ⌊(0 : ℝ)⌋ = (0 : ℤ) := by simp
    have h42 : ⌊(3 / 2 : ℝ)⌋ = (1 : ℤ) := by norm_num
    have eq1 : (⌊(0 : ℝ)⌋ : ℝ) = (0 : ℝ) := by simp
    have eq2 : (⌊(3 / 2 : ℝ)⌋ : ℝ) = (1 : ℝ) := by norm_num
    constructor
    · -- First equation
      norm_num [h41, h42, eq1, eq2, h4]
    · -- Second equation
      norm_num [h41, h42, eq1, eq2, h4, h6]
      <;> nlinarith