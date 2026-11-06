import Mathlib

theorem number_theory_2745 : ⌊(1 + √2)^4⌋ = 33 := by
  have h1 : (1 + Real.sqrt 2 : ℝ) ^ 4 = 17 + 12 * Real.sqrt 2 := by
    ring_nf
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [h2]
    have h4 : Real.sqrt 2 ^ 4 = 4 := by
      calc
        Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
        _ = 2 ^ 2 := by rw [h2]
        _ = 4 := by norm_num
    simp [h2, h3, h4]
    <;> ring_nf <;> norm_num [Real.sq_sqrt]
  rw [h1]
  have h2 : 33 ≤ (17 + 12 * Real.sqrt 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h3 : (17 + 12 * Real.sqrt 2 : ℝ) < (34 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      show Real.sqrt 2 < (17 / 12 : ℝ) by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try linarith