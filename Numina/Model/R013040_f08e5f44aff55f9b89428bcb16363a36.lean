import Mathlib

theorem algebra_4112 {x y : ℝ} (hy : 1 < y) (hxy : x * y = 1) (h : y ^ (y - 6 * x) = x ^ (y - 2 * x)) :
    x = 1 / 2 := by
  have hx1 : x > 0 := by
    nlinarith
  have hx2 : x = 1 / y := by 
    have hne : y ≠ 0 := by nlinarith
    field_simp [hne]
    <;> nlinarith
  rw [show x = 1 / y by linarith [hx2]] at h
  have eq5 : y ^ (y - 6 * (1 / y)) = (1 / y) ^ (y - 2 * (1 / y)) := by
    simpa using h
  have eq6 : y ^ (y - 6 * (1 / y)) = (y : ℝ) ^ ((y ^ 2 - 6) / y) := by
    have eq7 : y - 6 * (1 / y) = (y ^ 2 - 6) / y := by 
      field_simp [(show y ≠ 0 by linarith)]
      <;> ring
    rw [eq7]
  have h47 : (1 / y) ^ (y - 2 * (1 / y)) = (y : ℝ) ^ ((- (y ^ 2) + 2) / y) := by
    have h41 : (1 / y : ℝ) = (y : ℝ) ^ (-1 : ℝ) := by
      field_simp [Real.rpow_neg_one]
      <;> ring_nf <;> field_simp
    have h42 : (1 / y : ℝ) ^ (y - 2 * (1 / y)) = ((y : ℝ) ^ (-1 : ℝ)) ^ (y - 2 * (1 / y)) := by
      rw [h41]
    rw [h42]
    have h43 : ((y : ℝ) ^ (-1 : ℝ)) ^ (y - 2 * (1 / y)) = (y : ℝ) ^ ((-1 : ℝ) * (y - 2 * (1 / y))) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith [show 0 < y by linarith]
    rw [h43]
    have h44 : (-1 : ℝ) * (y - 2 * (1 / y)) = (- (y ^ 2) + 2) / y := by
      field_simp [(show y ≠ 0 by linarith)]
      <;> ring_nf
      <;> field_simp
      <;> nlinarith
      all_goals try { norm_num }
      all_goals try { tauto }
    rw [h44]
    all_goals try { norm_num }
    all_goals try { tauto }
  have eq8 : (y : ℝ) ^ ((y ^ 2 - 6) / y) = (y : ℝ) ^ ((- (y ^ 2) + 2) / y) := by
    have eq9 : (y : ℝ) ^ (y - 6 * (1 / y)) = (1 / y) ^ (y - 2 * (1 / y)) := eq5
    rw [eq6] at eq9
    rw [h47] at eq9
    all_goals try { norm_num at eq9 ⊢ }
    all_goals try { linarith }
  have eq2 : (y ^ 2 - 6) / y = (- (y ^ 2) + 2) / y := by
    apply_fun (Real.logb y) at eq8
    have eq4 : Real.logb y ((y : ℝ) ^ ((y ^ 2 - 6) / y)) = (y ^ 2 - 6) / y := by
      rw [Real.logb_rpow]
      all_goals nlinarith
    have eq5 : Real.logb y ((y : ℝ) ^ ((- (y ^ 2) + 2) / y)) = (- (y ^ 2) + 2) / y := by
      rw [Real.logb_rpow]
      all_goals nlinarith
    rw [eq4] at eq8
    rw [eq5] at eq8
    all_goals try { linarith }
    all_goals try { norm_num }
    all_goals try { tauto }
  have eq3 : y ^ 2 - 6 = - (y ^ 2) + 2 := by
    have eq8 : (y ^ 2 - 6) / y = (- (y ^ 2) + 2) / y := eq2
    field_simp [(show y ≠ 0 by linarith)] at eq8
    all_goals try { nlinarith }
    all_goals try { norm_num }
    all_goals try { tauto }
  have eq4 : 2 * (y ^2) = 8 := by
    nlinarith
  have hy4 : y^2 = 4 := by
    nlinarith
  have h14 : y = 2 := by
    nlinarith [sq_nonneg (y - 2), sq_nonneg (y + 2)]
  have hx4 : x * y = 1 := hxy
  have hx5 : x = 1 / 2 := by
    rw [show y = 2 by linarith [h14]] at hx4
    have hx6 : x = 1/2 := by
      nlinarith
    linarith
  linarith [hx5]