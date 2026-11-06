import Mathlib

open Real

theorem algebra_1623 {a : ℝ} (ha : a = 1996 / (sqrt 1997 - 1)) : a ^ 5 - 2 * a ^ 4 - 1996 * a ^ 3 = 0 := by
  have h1 : a = Real.sqrt 1997 + 1 := by
    rw [ha]
    have hne : sqrt 1997 - 1 ≠ 0 := by
      have h2 : sqrt 1997 > 1 := by
        have h3 : sqrt 1997 > sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h4 : sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
        linarith [h3, h4]
      linarith
    have hsqrt_pos : sqrt 1997 > 0 := Real.sqrt_pos.mpr (by norm_num : (1997 : ℝ) > 0)
    field_simp [hne]
    ring_nf
    <;> rw [Real.sq_sqrt (by norm_num)]
    <;> ring_nf <;> norm_num
    <;> ring
  have h2 : a ^ 2 = 2 * a + 1996 := by 
    rw [h1]
    nlinarith [Real.sq_sqrt (show (1997 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (1997 : ℝ) > 0 by norm_num)]
  have h3 : a ^ 3 = 2000 * a + 3992 := by 
    calc 
      a ^ 3 = a * a ^ 2 := by ring 
      _ = a * (2 * a + 1996) := by rw [h2]
      _ = 2 * a ^ 2 + 1996 * a := by ring 
      _ = 2 * (2 * a + 1996) + 1996 * a := by rw [h2]
      _ = 2000 * a + 3992 := by ring
  have h4 : a ^ 4 = 7992 * a + 3992000 := by
    calc 
      a ^ 4 = (a ^ 2) ^ 2 := by ring 
      _ = (2 * a + 1996) ^ 2 := by rw [h2]
      _ = 7992 * a + 3992000 := by nlinarith [h2]
  have h5 : a ^ 5 = 4007984 * a + 7992 * 1996 := by
    calc 
      a ^ 5 = a * a ^ 4 := by ring 
      _ = a * (7992 * a + 3992000) := by rw [h4]
      _ = 7992 * a ^ 2 + 3992000 * a := by ring 
      _ = 7992 * (2 * a + 1996) + 3992000 * a := by rw [h2]
      _ = 4007984 * a + 7992 * 1996 := by ring
  rw [h5, h4, h3]
  nlinarith