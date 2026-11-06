import Mathlib

theorem algebra_100141 : round (((1 + Real.sqrt 3)^4 / 4) : ℝ) = 14 := by
  have h1 : (1 + Real.sqrt 3) ^ 2 = 4 + 2 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

  have h2 : (1 + Real.sqrt 3) ^ 4 = (4 + 2 * Real.sqrt 3) ^ 2 := by
    calc
      (1 + Real.sqrt 3) ^ 4 = ((1 + Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = (4 + 2 * Real.sqrt 3) ^ 2 := by rw [h1]

  have h3 : (1 + Real.sqrt 3) ^ 4 = 28 + 16 * Real.sqrt 3 := by
    rw [h2]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

  have h4 : (1 + Real.sqrt 3) ^ 4 / 4 = 7 + 4 * Real.sqrt 3 := by
    rw [h3]
    ring_nf

  rw [h4]
  have h5 : 1.732 < Real.sqrt 3 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h6 : Real.sqrt 3 < 1.733 := by
    rw [Real.sqrt_lt] <;> norm_num
  rw [round_eq]
  simp only [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith [h5, h6]