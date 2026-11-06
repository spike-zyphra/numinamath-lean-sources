import Mathlib

theorem algebra_146839 (a b c d : ℝ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a)
    (x y z : ℝ)
    (hx : x = Real.sqrt (a * b) + Real.sqrt (c * d))
    (hy : y = Real.sqrt (a * c) + Real.sqrt (b * d))
    (hz : z = Real.sqrt (a * d) + Real.sqrt (b * c)) :
    x > y ∧ y > z := by
  have h1 : 0 < d := ha
  have h2 : 0 < c := by linarith
  have h3 : 0 < b := by linarith
  have h4 : 0 < a := by linarith
  have h5 : x > y := by
    rw [hx, hy]
    have h6 : 0 ≤ Real.sqrt (a * b) + Real.sqrt (c * d) := by positivity
    have h7 : 0 ≤ Real.sqrt (a * c) + Real.sqrt (b * d) := by positivity
    have h8 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 > (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 := by
      have h9 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 = (Real.sqrt (a * b)) ^ 2 + (Real.sqrt (c * d)) ^ 2 + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by ring
      have h10 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = (Real.sqrt (a * c)) ^ 2 + (Real.sqrt (b * d)) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
      rw [h9, h10]
      have h11 : (Real.sqrt (a * b)) ^ 2 = a * b := by
        rw [Real.sq_sqrt]
        positivity
      have h12 : (Real.sqrt (c * d)) ^ 2 = c * d := by
        rw [Real.sq_sqrt]
        positivity
      have h13 : (Real.sqrt (a * c)) ^ 2 = a * c := by
        rw [Real.sq_sqrt]
        positivity
      have h14 : (Real.sqrt (b * d)) ^ 2 = b * d := by
        rw [Real.sq_sqrt]
        positivity
      rw [h11, h12, h13, h14]
      have h15 : 0 < a - d := by linarith
      have h16 : 0 < b - c := by linarith
      have h17 : a * b + c * d > a * c + b * d := by
        nlinarith [mul_pos (sub_pos.mpr (by linarith : (0 : ℝ) < a - d)) (sub_pos.mpr (by linarith : (0 : ℝ) < b - c)), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < c by linarith), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < d by linarith), mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < c by linarith), mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < d by linarith), mul_pos (show (0 : ℝ) < c by linarith) (show (0 : ℝ) < d by linarith)]
      nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ c * d by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ a * c by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ b * d by positivity), mul_nonneg (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg (c * d)), mul_nonneg (Real.sqrt_nonneg (a * c)) (Real.sqrt_nonneg (b * d)), sq_nonneg (Real.sqrt (a * b) - Real.sqrt (a * c)), sq_nonneg (Real.sqrt (c * d) - Real.sqrt (b * d)), h17]
    nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), h8, sq_nonneg (Real.sqrt (a * b) + Real.sqrt (c * d) - (Real.sqrt (a * c) + Real.sqrt (b * d)))
    ]
  have h6 : y > z := by
    rw [hy, hz]
    have h6 : 0 ≤ Real.sqrt (a * c) + Real.sqrt (b * d) := by positivity
    have h7 : 0 ≤ Real.sqrt (a * d) + Real.sqrt (b * c) := by positivity
    have h8 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 > (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2 := by
      have h9 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = (Real.sqrt (a * c)) ^ 2 + (Real.sqrt (b * d)) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
      have h10 : (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2 = (Real.sqrt (a * d)) ^ 2 + (Real.sqrt (b * c)) ^ 2 + 2 * (Real.sqrt (a * d) * Real.sqrt (b * c)) := by ring
      rw [h9, h10]
      have h11 : (Real.sqrt (a * c)) ^ 2 = a * c := by
        rw [Real.sq_sqrt]
        positivity
      have h12 : (Real.sqrt (b * d)) ^ 2 = b * d := by
        rw [Real.sq_sqrt]
        positivity
      have h13 : (Real.sqrt (a * d)) ^ 2 = a * d := by
        rw [Real.sq_sqrt]
        positivity
      have h14 : (Real.sqrt (b * c)) ^ 2 = b * c := by
        rw [Real.sq_sqrt]
        positivity
      rw [h11, h12, h13, h14]
      have h17 : a * c + b * d > a * d + b * c := by
        nlinarith [mul_pos (show (0 : ℝ) < a - b by linarith) (show (0 : ℝ) < c - d by linarith), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < c by linarith), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < d by linarith), mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < c by linarith), mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < d by linarith), mul_pos (show (0 : ℝ) < c by linarith) (show (0 : ℝ) < d by linarith)]
      nlinarith [Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c), Real.sq_sqrt (show (0 : ℝ) ≤ a * c by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ b * d by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ a * d by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ b * c by positivity), mul_nonneg (Real.sqrt_nonneg (a * c)) (Real.sqrt_nonneg (b * d)), mul_nonneg (Real.sqrt_nonneg (a * d)) (Real.sqrt_nonneg (b * c)), sq_nonneg (Real.sqrt (a * c) - Real.sqrt (a * d)), sq_nonneg (Real.sqrt (b * d) - Real.sqrt (b * c)), h17]
    nlinarith [Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c), h8, sq_nonneg (Real.sqrt (a * c) + Real.sqrt (b * d) - (Real.sqrt (a * d) + Real.sqrt (b * c))
    )
    ]
  constructor
  · exact h5
  · exact h6