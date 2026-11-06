import Mathlib

theorem algebra_283098 (i : ℂ) (h : i^2 = -1) :
    (1 + i)^20 - (1 - i)^20 = 0 := by
  have h1 : (1 + i) ^ 2 = 2 * i := by
    calc
      (1 + i) ^ 2 = 1 ^ 2 + 2 * 1 * i + i ^ 2 := by ring
      _ = 1 + 2 * i + (-1) := by simp [h]
      _ = 2 * i := by ring
  have h2 : (1 - i) ^ 2 = -2 * i := by
    calc
      (1 - i) ^ 2 = 1 ^ 2 - 2 * 1 * i + i ^ 2 := by ring
      _ = 1 - 2 * i + (-1) := by simp [h]
      _ = -2 * i := by ring
  have h3 : (1 + i) ^ 20 = ((1 + i) ^ 2) ^ 10 := by ring
  have h4 : (1 - i) ^ 20 = ((1 - i) ^ 2) ^ 10 := by ring
  rw [h3, h4, h1, h2]
  have h_i4 : i ^ 4 = 1 := by
    calc
      i ^ 4 = (i ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [h]
      _ = 1 := by norm_num
  have h_i10 : i ^ 10 = -1 := by
    calc
      i ^ 10 = i ^ (4 * 2 + 2) := by simp
      _ = (i ^ 4) ^ 2 * i ^ 2 := by ring
      _ = (1) ^ 2 * (-1) := by rw [h_i4, h]
      _ = -1 := by ring
  have h5 : (2 * i) ^ 10 = - (2 ^ 10 : ℂ) := by
    calc
      (2 * i) ^ 10 = 2 ^ 10 * (i ^ 10) := by ring_nf
      _ = 2 ^ 10 * (-1) := by rw [h_i10]
      _ = - (2 ^ 10 : ℂ) := by ring
  have h6 : (-2 * i) ^ 10 = - (2 ^ 10 : ℂ) := by
    calc
      (-2 * i) ^ 10 = (-2) ^ 10 * (i ^ 10) := by ring_nf
      _ = (2 : ℂ) ^ 10 * (-1) := by
        simp [pow_succ, h_i10]
        <;> ring_nf
        <;> norm_num [h_i10]
      _ = - (2 ^ 10 : ℂ) := by ring_nf
  rw [h5, h6]
  ring_nf