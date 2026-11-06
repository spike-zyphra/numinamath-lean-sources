import Mathlib

theorem algebra_266974 {m n r t : ℚ} (hmn : m / n = 4 / 3) (hru : r / t = 9 / 14) :
    (3 * m * r - n * t) / (4 * n * t - 7 * m * r) = -11 / 14 := by 
  have h1 : n ≠ 0 := by 
    by_contra h
    rw [h] at hmn
    norm_num at hmn
  have h2 : t ≠ 0 := by
    by_contra h
    rw [h] at hru
    norm_num at hru
  have h3 : m = 4 / 3 * n := by
    field_simp [h1] at hmn
    linarith
  have h4 : r = 9 / 14 * t := by
    field_simp [h2] at hru
    linarith
  have num_eq : 3 * m * r - n * t = 11 / 7 * (n * t) := by
    rw [h3, h4]
    linarith 
  have denom_eq : 4 * n * t - 7 * m * r = -2 * (n * t) := by 
    rw [h3, h4]
    linarith
  have h5 : n * t ≠ 0 := by
    apply mul_ne_zero
    exact h1
    exact h2
  rw [num_eq, denom_eq]
  field_simp [h5]
  <;> linarith