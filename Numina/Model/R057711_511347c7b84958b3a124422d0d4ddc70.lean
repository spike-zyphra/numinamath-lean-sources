import Mathlib

theorem algebra_319363 : √((3 + √5) / 2) - √((3 - √5) / 2) = 1 := by 
  have h1 : √((3 + √5) / 2) = (1 + √5) / 2 := by
    have h2 : ((1 + √5) / 2) ^ 2 = (3 + √5) / 2 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h3 : (3 + √5) / 2 ≥ 0 := by
      positivity
    have h4 : ((1 + √5) / 2) ≥ 0 := by
      positivity
    rw [← h2]
    field_simp [Real.sqrt_sq]
    <;> ring_nf <;> norm_num
    <;> linarith [Real.sqrt_nonneg 5]

  have h1' : √((3 - √5) / 2) = ( √5 - 1 ) / 2 := by
    have h2 : ((√5 - 1) / 2) ^ 2 = (3 - √5) / 2 := by 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h3 : (3 - √5) / 2 ≥ 0 := by
      have h5 : Real.sqrt 5 < 3 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
      nlinarith [Real.sqrt_nonneg 5]

    have h4 : (√5 - 1) / 2 ≥ 0 := by 
      have h6 : Real.sqrt 5 > 1 := by
        have h6 : 1 < Real.sqrt 5 := by
          rw [Real.lt_sqrt] <;> norm_num
        linarith
      have h7 : Real.sqrt 5 - 1 > 0 := by linarith [h6]
      linarith [h7]

    rw [← h2]
    field_simp [Real.sqrt_sq]
    <;> ring_nf <;> norm_num
    <;> linarith [Real.sqrt_nonneg 5]

  rw [h1, h1']
  -- Calculate the subtraction
  field_simp
  <;> ring_nf <;> norm_num
  <;> linarith [Real.sqrt_nonneg 5]