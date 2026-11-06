import Mathlib

open Real

theorem algebra_181656 : ((sqrt 666 + sqrt 888)^2 - sqrt (666^2 + 888^2)) / 444 = 1 + 2 * sqrt 3 := by
  have h1 : sqrt (666^2 + 888^2) = 1110 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : sqrt 666 * sqrt 888 = 444 * Real.sqrt 3 := by
    have h3 : sqrt 666 * sqrt 888 = Real.sqrt (666 * (888 : ℝ)) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h3]
    have h4 : Real.sqrt (666 * (888 : ℝ)) = 444 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h4]
  have h5 : (sqrt 666 + sqrt 888) ^ 2 = 1554 + 2 * (444 * Real.sqrt 3) := by
    calc
      (sqrt 666 + sqrt 888) ^ 2
          = (sqrt 666) ^ 2 + (sqrt 888) ^ 2 + 2 * (sqrt 666 * sqrt 888) := by ring
      _ = 666 + 888 + 2 * (sqrt 666 * sqrt 888) := by
        have h6 : (sqrt 666) ^ 2 = 666 := Real.sq_sqrt (by norm_num)
        have h7 : (sqrt 888) ^ 2 = 888 := Real.sq_sqrt (by norm_num)
        rw [h6, h7]
      _ = 666 + 888 + 2 * (444 * Real.sqrt 3) := by
        rw [h2]
      _ = 1554 + 2 * (444 * Real.sqrt 3) := by norm_num
  have h6 : (sqrt 666 + sqrt 888) ^ 2 - sqrt (666^2 + 888^2) = 444 + 2 * (444 * Real.sqrt 3) := by
    rw [h5, h1]
    all_goals norm_num
    <;> nlinarith
  calc
    ((sqrt 666 + sqrt 888) ^ 2 - sqrt (666^2 + 888^2)) / 444
        = (444 + 2 * (444 * Real.sqrt 3)) / 444 := by rw [h6]
    _ = (444 * (1 + 2 * Real.sqrt 3)) / 444 := by ring
    _ = 1 + 2 * Real.sqrt 3 := by
      field_simp
      <;> ring