import Mathlib

theorem algebra_14242 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) (hsum1 : x + 1 / z = 5) (hsum2 : y + 1 / x = 29) :
    z + 1 / y = 1 / 4 := by 
  have h1 : x * y * z = 1 := hxyz
  have h2 : z ≠ 0 := by linarith
  have h3 : x ≠ 0 := by linarith
  have h4 : y ≠ 0 := by nlinarith
  have h5' : 1 / z = x * y := by
    have hxyz' : x * y * z = 1 := hxyz
    have hne : z ≠ 0 := by linarith
    field_simp [hne, h3, h4]
    <;> nlinarith
    <;> field_simp [hne, h3, h4]
    <;> nlinarith
  have eq3 : x * (1 + y) = 5 := by
    have h6 : x + 1 / z = 5 := hsum1
    rw [h5'] at h6
    nlinarith
  have eq4 : y = 29 - 1 / x := by
    have h6 : y + 1 / x = 29 := hsum2
    field_simp [h3] at h6 ⊢
    nlinarith
  have eq5 : x = 1 / 5 := by
    rw [eq4] at eq3
    field_simp [h3] at eq3 ⊢
    nlinarith
  have eq6 : y = 24 := by
    rw [eq5] at eq4
    norm_num at eq4 ⊢
    nlinarith
  have eq7 : z = 5 / 24 := by
    rw [eq5, eq6] at hxyz
    nlinarith
  rw [eq7, eq6]
  norm_num
  <;> linarith
  all_goals norm_num
  <;> nlinarith
  <;> linarith
  <;> norm_num
  <;> nlinarith
  <;> linarith
  <;> norm_num
  <;> nlinarith
  <;> linarith
  all_goals linarith
  <;> tauto
  <;> nlinarith