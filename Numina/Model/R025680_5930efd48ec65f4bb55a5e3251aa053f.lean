import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_328045 : IsGreatest (range (λ x => 2 * (2 * cos x + 1) * (sin x)^2 + cos (3 * x))) (17 / 8) := by
  constructor
  · -- First part: Show 17/8 is in the range
    use Real.arccos (1 / 4)
    have h1 : cos (Real.arccos (1 / 4)) = 1 / 4 := by
      apply Real.cos_arccos
      all_goals norm_num
    have h2 : sin (Real.arccos (1 / 4)) ^ 2 = 15 / 16 := by
      have h3 : sin (Real.arccos (1 / 4)) ^ 2 + cos (Real.arccos (1 / 4)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.arccos (1 / 4))
      rw [h1] at h3
      nlinarith [show sin (Real.arccos (1 / 4)) ^ 2 ≥ 0 by positivity]
    have h3 : cos (3 * Real.arccos (1 / 4)) = -11 / 16 := by
      have h4 : cos (3 * Real.arccos (1 / 4)) = 4 * (cos (Real.arccos (1 / 4))) ^ 3 - 3 * (cos (Real.arccos (1 / 4))) := by
        rw [cos_three_mul]
      rw [h4, h1]
      norm_num
    simp [h1, h2, h3]
    all_goals nlinarith
  · -- Second part: Show 17/8 is the greatest
    intro y
    rintro ⟨x, hx⟩
    simp at hx
    have h4 : cos (3 * x) = 4 * (cos x) ^ 3 - 3 * (cos x) := by
      have h5 : cos (3 * x) = 4 * (cos x) ^ 3 - 3 * (cos x) := by
        rw [cos_three_mul]
      exact h5
    rw [h4] at hx
    have h5 : 2 * (2 * cos x + 1) * (sin x) ^ 2 + (4 * (cos x) ^ 3 - 3 * (cos x)) = cos x + 2 - 2 * (cos x) ^ 2 := by
      have h6 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      have h7 : (sin x) ^ 2 = 1 - (cos x) ^ 2 := by linarith
      rw [h7]
      nlinarith [sq_nonneg (cos x - 1 / 4)]
    have h6 : cos x ≤ 1 := by
      apply cos_le_one
    have h7 : -1 ≤ cos x := by
      apply neg_one_le_cos
    have h8 : cos x + 2 - 2 * (cos x) ^ 2 ≤ 17 / 8 := by
      nlinarith [sq_nonneg (cos x - 1 / 4)]
    have h9 : y = cos x + 2 - 2 * (cos x) ^ 2 := by
      linarith [h5, hx]
    nlinarith [h9, h8]