import Mathlib

theorem algebra_4208 {x y z : ℝ} (h : x / 2 = y / 3) (h1 : y / 3 = z / 5) (h2 : z / 5 ≠ 0) :
    (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2) = 31 / 38 := by 
  have h3 : 3 * x = 2 * y := by
    field_simp at h
    linarith
  have h4 : y = (3 / 2) * x := by
    linarith
  have h5 : 5 * y = 3 * z := by 
    field_simp at h1
    linarith
  have h6 : z = (5 / 3) * y := by
    linarith
  have h7 : z = (5 / 2) * x := by 
    rw [h4] at h6
    linarith
  have eq1 : x * y + y * z + z * x = (31 / 4) * x ^ 2 := by 
    rw [h4, h7]
    linarith
  have eq2 : x ^ 2 + y ^ 2 + z ^ 2 = (38 / 4) * x ^ 2 := by 
    rw [h4, h7]
    linarith
  have hx_ne_zero : x ≠ 0 := by
    by_contra hx
    have h8 : x = 0 := hx
    have h9 : z = 0 := by 
      rw [h8] at h7
      linarith
    have h10 : z / 5 = 0 := by 
      rw [h9]
      norm_num
    contradiction
  have hx2_ne_zero : x ^ 2 ≠ 0 := by 
    apply pow_ne_zero 2
    exact hx_ne_zero
  rw [eq1, eq2]
  field_simp [hx2_ne_zero]
  <;> ring_nf <;> field_simp [hx2_ne_zero] <;> all_goals linarith
  all_goals norm_num