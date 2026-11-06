import Mathlib

open Real


lemma lemma_1 (x : ℝ) (hx : 0 < x ∧ x < 1) (y : ℝ) (hy : y < 0) : x ^ y > 1 := by
  have h1 : 0 < x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : Real.log x < 0 := by
    have h4 : Real.log x < Real.log (1 : ℝ) := by
      apply Real.log_lt_log
      all_goals linarith
    have h5 : Real.log (1 : ℝ) = 0 := Real.log_one
    linarith
  have h6 : y * Real.log x > 0 := by
    nlinarith
  have h7 : x ^ y = Real.exp (y * Real.log x) := by
    rw [Real.rpow_def_of_pos h1]
    field_simp [mul_comm]
    <;> ring
  rw [h7]
  have h8 : Real.exp (y * Real.log x) > Real.exp (0 : ℝ) := by
    apply Real.exp_strictMono
    all_goals nlinarith
  have h9 : Real.exp (0 : ℝ) = 1 := Real.exp_zero
  linarith


theorem algebra_129622 : (1 / sqrt 2) ^ (-1 / sqrt 2) > 1 := by
  have h1 : 1 / sqrt 2 < (1 : ℝ) := by
    have h2 : sqrt 2 > (1 : ℝ) := by
      have h6 : 1 < sqrt 2 := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith
    have h7 : sqrt 2 > (1 : ℝ) := by
      have h6 : 1 < sqrt 2 := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith
    have h7' : sqrt 2 > 0 := by positivity
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hx10 : (0 : ℝ) < (1 / sqrt 2 : ℝ) := by
    positivity
  have hx11 : (1 / sqrt 2 : ℝ) < (1 : ℝ) := h1
  have hx20 : (-1 / sqrt 2 : ℝ) < (0 : ℝ) := by
    apply div_neg_of_neg_of_pos
    · norm_num
    · -- Show sqrt 2 > 0
      positivity
  -- combine
  have hx1 : 0 < (1 / sqrt 2 : ℝ) ∧ (1 / sqrt 2 : ℝ) < 1 := by
    constructor
    · linarith [hx10]
    · linarith [hx11]
  have hx2 : (-1 / sqrt 2 : ℝ) < 0 := by linarith [hx20]
  have hx3 : (1 / sqrt 2 : ℝ) ^ (-1 / sqrt 2) > (1 : ℝ) := by
    apply lemma_1 (1 / sqrt 2) hx1 (-1 / sqrt 2) hx2
  linarith