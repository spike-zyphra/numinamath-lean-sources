import Mathlib

theorem algebra_321689 {a b c d : ℝ} (ha : 0 < a) (hd : 0 < d) (hdc : d < c) (hcb : c < b) (hba : b < a)
    (x y z : ℝ) (hx : x = Real.sqrt (a * b) + Real.sqrt (c * d)) (hy : y = Real.sqrt (a * c) + Real.sqrt (b * d))
    (hz : z = Real.sqrt (a * d) + Real.sqrt (b * c)) : z < y ∧ y < x := by

  have h1 : 0 < d := by linarith
  have h2 : 0 < c := by nlinarith
  have h3 : 0 < b := by nlinarith
  have h4 : 0 < a := by nlinarith
  have h7 : Real.sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
  have h8 : Real.sqrt (c * d) ≥ 0 := Real.sqrt_nonneg (c * d)
  have h5 : Real.sqrt (a * c) ≥ 0 := Real.sqrt_nonneg (a * c)
  have h6 : Real.sqrt (b * d) ≥ 0 := Real.sqrt_nonneg (b * d)
  have h9 : Real.sqrt (a * d) ≥ 0 := Real.sqrt_nonneg (a * d)
  have h10 : Real.sqrt (b * c) ≥ 0 := Real.sqrt_nonneg (b * c)

  have h11 : y > z := by
    rw [hy, hz]
    have h12 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 > (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2 := by
      have h13 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = Real.sqrt (a * c) ^ 2 + Real.sqrt (b * d) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
      have h14 : (Real.sqrt (a * d) + Real.sqrt (b * c)) ^ 2 = Real.sqrt (a * d) ^ 2 + Real.sqrt (b * c) ^ 2 + 2 * (Real.sqrt (a * d) * Real.sqrt (b * c)) := by ring
      rw [h13, h14]
      have h15 : Real.sqrt (a * c) ^ 2 = a * c := by
        rw [Real.sq_sqrt]
        nlinarith
      have h16 : Real.sqrt (b * d) ^ 2 = b * d := by
        rw [Real.sq_sqrt]
        nlinarith
      have h17 : Real.sqrt (a * d) ^ 2 = a * d := by
        rw [Real.sq_sqrt]
        nlinarith
      have h18 : Real.sqrt (b * c) ^ 2 = b * c := by
        rw [Real.sq_sqrt]
        nlinarith
      rw [h15, h16, h17, h18]
      have h19 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt (a * c * b * d) := by
        have h19 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt ((a * c) * (b * d)) := by
          rw [← Real.sqrt_mul (by positivity)]
        have h21 : (a * c) * (b * d) = a * c * b * d := by ring
        rw [h21] at h19
        linarith [h19]
      have h20 : Real.sqrt (a * d) * Real.sqrt (b * c) = Real.sqrt (a * d * b * c) := by
        have h21 : Real.sqrt (a * d) * Real.sqrt (b * c) = Real.sqrt ((a * d) * (b * c)) := by
          rw [← Real.sqrt_mul (by positivity)]
        have h22 : (a * d) * (b * c) = a * d * b * c := by ring
        rw [h22] at h21
        linarith [h21]
      rw [h19, h20]
      have h21 : a * c + b * d + 2 * Real.sqrt (a * c * b * d) > a * d + b * c + 2 * Real.sqrt (a * d * b * c) := by
        have h23 : Real.sqrt (a * c * b * d) = Real.sqrt (a * b * c * d) := by ring_nf
        have h24 : Real.sqrt (a * d * b * c) = Real.sqrt (a * b * c * d) := by ring_nf
        rw [h23, h24]
        nlinarith [mul_pos (show 0 < a - b by linarith) (show 0 < c - d by linarith), mul_pos (show 0 < d by linarith) (show 0 < c - d by linarith)]
      nlinarith
    have h13 : Real.sqrt (a * c) + Real.sqrt (b * d) ≥ 0 := by positivity
    have h14 : Real.sqrt (a * d) + Real.sqrt (b * c) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c)]

  have h14 : x > y := by
    rw [hx, hy]
    have h15 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 > (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 := by
      have h13 : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 = Real.sqrt (a * b) ^ 2 + Real.sqrt (c * d) ^ 2 + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by ring
      have h14 : (Real.sqrt (a * c) + Real.sqrt (b * d)) ^ 2 = Real.sqrt (a * c) ^ 2 + Real.sqrt (b * d) ^ 2 + 2 * (Real.sqrt (a * c) * Real.sqrt (b * d)) := by ring
      rw [h13, h14]
      have h15 : Real.sqrt (a * b) ^ 2 = a * b := by
        rw [Real.sq_sqrt]
        nlinarith
      have h16 : Real.sqrt (c * d) ^ 2 = c * d := by
        rw [Real.sq_sqrt]
        nlinarith
      have h17 : Real.sqrt (a * c) ^ 2 = a * c := by
        rw [Real.sq_sqrt]
        nlinarith
      have h18 : Real.sqrt (b * d) ^ 2 = b * d := by
        rw [Real.sq_sqrt]
        nlinarith
      rw [h15, h16, h17, h18]
      have h19 : Real.sqrt (a * b) * Real.sqrt (c * d) = Real.sqrt (a * b * c * d) := by
        have h19 : Real.sqrt (a * b) * Real.sqrt (c * d) = Real.sqrt ((a * b) * (c * d)) := by
          rw [← Real.sqrt_mul (by positivity)]
        have h20 : (a * b) * (c * d) = a * b * c * d := by ring
        rw [h20] at h19
        linarith [h19]
      have h20 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt (a * c * b * d) := by
        have h21 : Real.sqrt (a * c) * Real.sqrt (b * d) = Real.sqrt ((a * c) * (b * d)) := by
          rw [← Real.sqrt_mul (by positivity)]
        have h22 : (a * c) * (b * d) = a * c * b * d := by ring
        rw [h22] at h21
        linarith [h21]
      rw [h19, h20]
      have h21 : a * b + c * d + 2 * Real.sqrt (a * b * c * d) > a * c + b * d + 2 * Real.sqrt (a * c * b * d) := by
        have h23 : Real.sqrt (a * b * c * d) = Real.sqrt (a * b * c * d) := by rfl
        have h24 : Real.sqrt (a * c * b * d) = Real.sqrt (a * b * c * d) := by ring_nf
        rw [h24]
        nlinarith [mul_pos (show 0 < a - d by linarith) (show 0 < b - c by linarith)]
      nlinarith
    have h13 : Real.sqrt (a * b) + Real.sqrt (c * d) ≥ 0 := by positivity
    have h14 : Real.sqrt (a * c) + Real.sqrt (b * d) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d)]

  constructor
  · linarith [h11]
  · linarith [h14]