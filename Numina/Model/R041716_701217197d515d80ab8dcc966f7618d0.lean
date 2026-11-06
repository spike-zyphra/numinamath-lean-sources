import Mathlib

theorem algebra_102710 : ⌊((3 + Real.sqrt 17) / 2)^6⌋ = 2040 := by
  have h1 : Real.sqrt 17 ^ 2 = 17 := by
    rw [Real.sq_sqrt]
    norm_num
  have h2 : ((3 + Real.sqrt 17) / 2) ^ 2 = 3 * ((3 + Real.sqrt 17) / 2) + 2 := by
    nlinarith [Real.sqrt_nonneg 17]
  have h3 : ((3 + Real.sqrt 17) / 2) ^ 3 = 11 * ((3 + Real.sqrt 17) / 2) + 6 := by
    calc
      ((3 + Real.sqrt 17) / 2) ^ 3 = ((3 + Real.sqrt 17) / 2) * ((3 + Real.sqrt 17) / 2) ^ 2 := by ring
      _ = ((3 + Real.sqrt 17) / 2) * (3 * ((3 + Real.sqrt 17) / 2) + 2) := by rw [h2]
      _ = 11 * ((3 + Real.sqrt 17) / 2) + 6 := by
        ring_nf
        <;> nlinarith [Real.sqrt_nonneg 17, h1]
  have h4 : ((3 + Real.sqrt 17) / 2) ^ 4 = 39 * ((3 + Real.sqrt 17) / 2) + 22 := by
    calc
      ((3 + Real.sqrt 17) / 2) ^ 4 = ((3 + Real.sqrt 17) / 2) * ((3 + Real.sqrt 17) / 2) ^ 3 := by ring
      _ = ((3 + Real.sqrt 17) / 2) * (11 * ((3 + Real.sqrt 17) / 2) + 6) := by rw [h3]
      _ = 39 * ((3 + Real.sqrt 17) / 2) + 22 := by
        ring_nf
        <;> nlinarith [Real.sqrt_nonneg 17, h1]
  have h5 : ((3 + Real.sqrt 17) / 2) ^ 5 = 139 * ((3 + Real.sqrt 17) / 2) + 78 := by
    calc
      ((3 + Real.sqrt 17) / 2) ^ 5 = ((3 + Real.sqrt 17) / 2) * ((3 + Real.sqrt 17) / 2) ^ 4 := by ring
      _ = ((3 + Real.sqrt 17) / 2) * (39 * ((3 + Real.sqrt 17) / 2) + 22) := by rw [h4]
      _ = 139 * ((3 + Real.sqrt 17) / 2) + 78 := by
        ring_nf
        <;> nlinarith [Real.sqrt_nonneg 17, h1]
  have h6 : ((3 + Real.sqrt 17) / 2) ^ 6 = 495 * ((3 + Real.sqrt 17) / 2) + 278 := by
    calc
      ((3 + Real.sqrt 17) / 2) ^ 6 = ((3 + Real.sqrt 17) / 2) * ((3 + Real.sqrt 17) / 2) ^ 5 := by ring
      _ = ((3 + Real.sqrt 17) / 2) * (139 * ((3 + Real.sqrt 17) / 2) + 78) := by rw [h5]
      _ = 495 * ((3 + Real.sqrt 17) / 2) + 278 := by
        ring_nf
        <;> nlinarith [Real.sqrt_nonneg 17, h1]
  rw [h6]
  have h7 : 2040 ≤ (495 * ((3 + Real.sqrt 17) / 2) + 278 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 17, Real.mul_self_sqrt (by norm_num : 0 ≤ (17 : ℝ)), sq_nonneg (Real.sqrt 17 - 4)]
  have h8 : (495 * ((3 + Real.sqrt 17) / 2) + 278 : ℝ) < (2041 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 17, Real.mul_self_sqrt (by norm_num : 0 ≤ (17 : ℝ)), sq_nonneg (Real.sqrt 17 - 4.123105625617661)]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith