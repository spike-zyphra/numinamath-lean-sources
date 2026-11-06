import Mathlib

open Real

theorem inequalities_223818 (x : Fin 5 → ℝ) (hx : ∀ i j, i < j → x i ≥ x j)
    (hx' : ∀ i, 0 ≤ x i) :
    (x 0 + x 1 + x 2 + x 3 + x 4)^2 ≥ 25 / 2 * (x 3^2 + x 4^2) ∧
    ((x 0 + x 1 + x 2 + x 3 + x 4)^2 = 25 / 2 * (x 3^2 + x 4^2) ↔
      (x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 = x 3 ∧ x 3 = x 4)) := by
  constructor
  · -- First part: proving the inequality
    have h1 : x 0 ≥ x 1 := by
      apply hx 0 1
      all_goals simp_all
    have h2 : x 1 ≥ x 2 := by
      apply hx 1 2
      all_goals simp_all
    have h3 : x 2 ≥ x 3 := by
      apply hx 2 3
      all_goals simp_all
    have h4 : x 3 ≥ x 4 := by
      apply hx 3 4
      all_goals simp_all

    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4),
        hx' 0, hx' 1, hx' 2, hx' 3, hx' 4]
  · -- Second part: proving the equality condition
    constructor
    · -- Forward direction: equality implies all variables equal
      intro h
      have h1 : x 0 ≥ x 1 := by
        apply hx 0 1
        all_goals simp_all
      have h2 : x 1 ≥ x 2 := by
        apply hx 1 2
        all_goals simp_all
      have h3 : x 2 ≥ x 3 := by
        apply hx 2 3
        all_goals simp_all
      have h4 : x 3 ≥ x 4 := by
        apply hx 3 4
        all_goals simp_all
      have h5 : 0 ≤ x 0 := hx' 0
      have h6 : 0 ≤ x 1 := hx' 1
      have h7 : 0 ≤ x 2 := hx' 2
      have h8 : 0 ≤ x 3 := hx' 3
      have h9 : 0 ≤ x 4 := hx' 4

      have h10 : x 0 = x 1 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4),
            hx' 0, hx' 1, hx' 2, hx' 3, hx' 4]
      have h11 : x 1 = x 2 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4),
            hx' 0, hx' 1, hx' 2, hx' 3, hx' 4]
      have h12 : x 2 = x 3 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4),
            hx' 0, hx' 1, hx' 2, hx' 3, hx' 4]
      have h13 : x 3 = x 4 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 2 - x 3), sq_nonneg (x 3 - x 4),
            hx' 0, hx' 1, hx' 2, hx' 3, hx' 4]
      simp [h10, h11, h12, h13]
      all_goals linarith
    · -- Backward direction: all variables equal implies equality
      rintro ⟨h1, h2, h3, h4⟩
      -- Substitutes variables from equations
      have h5 : x 0 = x 1 := by linarith
      have h6 : x 1 = x 2 := by linarith
      have h7 : x 2 = x 3 := by linarith
      have h8 : x 3 = x 4 := by linarith
      simp [h5, h6, h7, h8]
      all_goals nlinarith