import Mathlib

open Real

theorem algebra_181047 : 1 / (sqrt 15 + sqrt 13) + 1 / (sqrt 13 - sqrt 11) -
    (sqrt 5.5 - sqrt 7.5) / sqrt 2 = sqrt 15 := by

  have h1 : sqrt 15 + sqrt 13 > 0 := by
    positivity

  have h2 : sqrt 13 - sqrt 11 > 0 := by
    have h13 : sqrt 13 > sqrt 11 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    linarith

  have h5 : sqrt 2 > 0 := by
    positivity

  have eq1 : 1 / (sqrt 15 + sqrt 13) = (sqrt 15 - sqrt 13) / 2 := by
    field_simp [show sqrt 15 + sqrt 13 ≠ 0 by positivity
      , show sqrt 15 ^ 2 = 15 by rw [Real.sq_sqrt]; norm_num
      , show sqrt 13 ^ 2 = 13 by rw [Real.sq_sqrt]; norm_num
    ]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num

  have eq2 : 1 / (sqrt 13 - sqrt 11) = (sqrt 13 + sqrt 11) / 2 := by
    field_simp [show sqrt 13 - sqrt 11 ≠ 0 by
      have h1311 : sqrt 13 > sqrt 11 := by
        apply Real.sqrt_lt_sqrt
        all_goals norm_num
      linarith
    , show sqrt 13 ^ 2 = 13 by rw [Real.sq_sqrt]; norm_num
    , show sqrt 11 ^ 2 = 11 by rw [Real.sq_sqrt]; norm_num
    ]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num

  have eq3 : (sqrt 5.5 - sqrt 7.5) / sqrt 2 = (sqrt 11 - sqrt 15) / 2 := by
    have h55 : sqrt (5.5 : ℝ) = sqrt 11 / sqrt 2 := by
      have h4 : sqrt (5.5 : ℝ) = sqrt (11 / 2 : ℝ) := by
        norm_num
      rw [h4]
      have h5 : sqrt (11 / 2 : ℝ) = sqrt 11 / sqrt 2 := by
        field_simp [Real.sqrt_div]
      rw [h5]
    have h75 : sqrt (7.5 : ℝ) = sqrt 15 / sqrt 2 := by
      have h4 : sqrt (7.5 : ℝ) = sqrt (15 / 2 : ℝ) := by
        norm_num
      rw [h4]
      have h5 : sqrt (15 / 2 : ℝ) = sqrt 15 / sqrt 2 := by
        field_simp [Real.sqrt_div]
      rw [h5]
    rw [h55, h75]
    field_simp [Real.sqrt_eq_iff_mul_self_eq]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num

  rw [eq1, eq2, eq3]
  field_simp
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> nlinarith [Real.sqrt_nonneg 15, Real.sqrt_nonneg 13, Real.sqrt_nonneg 11, Real.sqrt_nonneg 2, Real.sqrt_nonneg 5.5, Real.sqrt_nonneg 7.5]