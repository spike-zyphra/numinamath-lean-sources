import Mathlib

open Real

theorem number_theory_187324 {z : ℝ} (hz : z = log (7 - 4 * sqrt 3) / log (2 - sqrt 3)) :
    ∃ q : ℚ, z = q := by
  use (2 : ℚ)
  rw [hz]
  have h1 : sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h7 : log (7 - 4 * sqrt 3) = 2 * log (2 - sqrt 3) := by
    have h8 : (7 - 4 * sqrt 3 : ℝ) = (2 - sqrt 3 : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (sqrt 3 - 2)]
    have h9 : log (7 - 4 * sqrt 3 : ℝ) = log ((2 - sqrt 3 : ℝ) ^ 2) := by
      rw [h8]
    have h10 : log ((2 - sqrt 3 : ℝ) ^ 2) = 2 * log (2 - sqrt 3 : ℝ) := by
      simp [log_pow]
    rw [h9, h10]
  have h11 : log (2 - sqrt 3) ≠ 0 := by
    have h12 : 2 - sqrt 3 > 0 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (sqrt 3 - 2), h1]
    have h14 : 2 - sqrt 3 ≠ 1 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    by_contra h
    have h15 : log (2 - sqrt 3) = 0 := by linarith [h]
    have h17 : (2 - sqrt 3 : ℝ) = 1 := by
      have h18 : log (2 - sqrt 3) = 0 := by linarith [h15]
      rw [log_eq_zero] at h18
      rcases h18 with (r | r | r)
      · linarith [r, h12]
      · linarith [r, h12]
      · nlinarith [h12, r]
    contradiction
  rw [h7]
  field_simp [h11]
  <;> ring