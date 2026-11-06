import Mathlib

theorem algebra_302311 {x y : ℝ} (hx : x = 1 / (2 + √3)) (hy : y = 1 / (2 - √3)) :
    x^3 + 12 * x * y + y^3 = 64 := by 
  have h1 : x = 2 - √3 := by 
    rw [hx]
    have h1 : (2 + √3) ≠ 0 := by 
      by_contra h
      have h2 : √3 = -2 := by linarith 
      have h3 : √3 ≥ 0 := Real.sqrt_nonneg 3 
      have h4 : -2 ≥ 0 := by linarith [h2, h3]
      linarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), h4]
    field_simp [h1]
    <;> ring_nf <;> norm_num 
    <;> ring_nf <;> norm_num 
  have h2 : y = 2 + √3 := by 
    rw [hy]
    have h2 : (2 - √3) ≠ 0 := by 
      by_contra h
      have h2 : √3 = 2 := by linarith 
      have h3 : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
      have h4 : √3 ≥ 0 := Real.sqrt_nonneg 3
      nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    field_simp [h2]
    <;> ring_nf <;> norm_num 
    <;> ring_nf <;> norm_num 
  rw [h1, h2]
  have h3 : (2 - √3) + (2 + √3) = 4 := by ring
  have h4 : (2 - √3) * (2 + √3) = 1 := by 
    nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  nlinarith [sq_nonneg ((2 - √3) - (2 + √3)), sq_nonneg ((2 - √3) + (2 + √3)), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), h3, h4]