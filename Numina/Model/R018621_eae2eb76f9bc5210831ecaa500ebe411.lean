import Mathlib

theorem algebra_272390 (m : ℕ) (a b : ℤ)
    (ha : a = 2019^(m + 1) - 2019^m)
    (hb : b = 2019^(m + 2) - 2019^(m + 1)) :
    b / a = 2019 := by
  rw [ha, hb]
  have h1 : ((2019 : ℤ) ^ (m + 2) - (2019 : ℤ) ^ (m + 1)) = 2019 * ((2019 : ℤ) ^ (m + 1) - (2019 : ℤ) ^ m) := by
    cases m with
    | zero =>
      all_goals
        norm_num
    | succ m =>
      simp [pow_succ, pow_add, mul_add, mul_comm, mul_assoc]
      <;> ring_nf
      <;> norm_num
      all_goals try omega

  have h5 : ((2019 : ℤ) ^ (m + 1) - (2019 : ℤ) ^ m) ≠ 0 := by
    have h2019 : (2019 : ℤ) > 1 := by
      norm_num
    have eq4 : ((2019 : ℤ) ^ (m + 1) - (2019 : ℤ) ^ m) = (2019 : ℤ) ^ m * (2018) := by 
      rw [pow_succ]
      <;> ring_nf
      <;> omega
    rw [eq4]
    have pos1 : (2019 : ℤ) ^ m > 0 := by
      positivity
    nlinarith
  
  rw [h1]
  field_simp [h5]
  <;> ring_nf <;> omega