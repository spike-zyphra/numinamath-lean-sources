import Mathlib

theorem algebra_97513 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x > y) (h : y > 0) :
    x ^ y * y ^ x / (y ^ y * x ^ x) = (x / y) ^ (y - x) := by
  have h1 : x ^ y * y ^ x / (y ^ y * x ^ x) = x ^ (y - x) * y ^ (x - y) := by
    have h2 : x ^ y * y ^ x / (y ^ y * x ^ x) = (x ^ y / x ^ x) * (y ^ x / y ^ y) := by
      field_simp
      <;> ring
      <;> ring
      <;> field_simp
      <;> ring
      <;> ring_nf
      <;> norm_num
      <;> nlinarith
    have h4 : x ^ y / x ^ x = x ^ (y - x) := by
      have h5 : x ^ (y - x) = x ^ y / x ^ x := by
        rw [← Real.rpow_sub]
        ring_nf
        all_goals linarith
      linarith [h5]
    have h3 : y ^ x / y ^ y = y ^ (x - y) := by
      have h4 : y ^ (x - y) = y ^ x / y ^ y := by
        rw [← Real.rpow_sub]
        ring_nf
        all_goals linarith
      linarith [h4]
    rw [h2, h4, h3]
    <;> ring_nf
    <;> norm_num
    <;> nlinarith
    all_goals linarith
    all_goals nlinarith
  rw [h1]
  -- Convert x^(y - x) * y^(x - y) to (x / y) ^ (y - x)
  have h2 : (x / y) ^ (y - x) = (x ^ (y - x)) / (y ^ (y - x)) := by
    rw [← Real.div_rpow]
    all_goals linarith
  have h4 : y ^ (x - y) = 1 / (y ^ (y - x)) := by
    have h5 : y ^ (x - y) = y ^ (-(y - x)) := by ring_nf
    rw [h5]
    rw [show y ^ (-(y - x)) = 1 / y ^ (y - x) by rw [Real.rpow_neg]; field_simp; all_goals linarith]
  rw [h2]
  rw [h4]
  field_simp
  <;> ring_nf
  <;> norm_num
  <;> nlinarith
  all_goals linarith