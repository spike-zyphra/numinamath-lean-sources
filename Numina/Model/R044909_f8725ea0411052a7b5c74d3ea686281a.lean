import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_165066 {f : ℝ → ℝ} (hf : f = λ x => (x + 1)^2 / (x^2 + 1)) :
    StrictMonoOn f {x | -1 < x ∧ x < 1} := by
  intro x hx y hy hxy
  have hx1 : -1 < x := hx.1
  have hx2 : x < 1 := hx.2
  have hy1 : -1 < y := hy.1
  have hy2 : y < 1 := hy.2
  have h1 : x < y := hxy
  have h2 : f x < f y := by
    rw [hf]
    have pos1 : (x ^ 2 + 1 : ℝ) > 0 := by
      nlinarith
    have pos2 : (y ^ 2 + 1 : ℝ) > 0 := by
      nlinarith
    have h4 : (x + 1) ^ 2 * (y ^ 2 + 1) < (y + 1) ^ 2 * (x ^ 2 + 1) := by
      have h5 : x * y < 1 := by
        nlinarith [mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy2), mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hx2), mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hy2), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1)]
      have h6 : x < y := h1
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < y - x by linarith), sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_pos_of_pos (show (0 : ℝ) < 1 - x * y by nlinarith), mul_pos (show (0 : ℝ) < y - x by linarith) (show (0 : ℝ) < 1 - x * y by nlinarith)]
    have h3 : (x + 1) ^ 2 / (x ^ 2 + 1) < (y + 1) ^ 2 / (y ^ 2 + 1) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      linarith
    simpa using h3
  exact h2
  all_goals linarith