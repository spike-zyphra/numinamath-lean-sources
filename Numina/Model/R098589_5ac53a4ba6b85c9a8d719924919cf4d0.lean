import Mathlib

open Real

theorem algebra_305926 {a b c d : ℝ} (ha : 0 < a) (hd : 0 < d) (hdc : d < c) (hcb : c < b)
    (hba : b < a) (x y z : ℝ)
    (hx : x = sqrt (a * b) + sqrt (c * d))
    (hy : y = sqrt (a * c) + sqrt (b * d))
    (hz : z = sqrt (a * d) + sqrt (b * c)) :
    z < y ∧ y < x := by

  have h1 : 0 < c := by linarith
  have h2 : 0 < b := by linarith
  have h3 : z < y := by
    have hz_pos : 0 < z := by
      have h4 : 0 < sqrt (a * d) := by
        apply Real.sqrt_pos.2
        nlinarith
      have h5 : 0 < sqrt (b * c) := by
        apply Real.sqrt_pos.2
        nlinarith
      linarith [hz, h4, h5]
    have hy_pos : 0 < y := by
      have h4 : 0 < sqrt (a * c) := by
        apply Real.sqrt_pos.2
        nlinarith
      have h5 : 0 < sqrt (b * d) := by
        apply Real.sqrt_pos.2
        nlinarith
      linarith [hy, h4, h5]
    have h6 : z ^ 2 < y ^ 2 := by
      rw [hz, hy]
      have h7 : (sqrt (a * d) + sqrt (b * c)) ^ 2 = a * d + b * c + 2 * (sqrt (a * b * c * d)) := by
        calc
          (sqrt (a * d) + sqrt (b * c)) ^ 2
              = (sqrt (a * d)) ^ 2 + (sqrt (b * c)) ^ 2 + 2 * (sqrt (a * d) * sqrt (b * c)) := by ring
          _ = a * d + b * c + 2 * (sqrt (a * d) * sqrt (b * c)) := by
            have h8 : (sqrt (a * d)) ^ 2 = a * d := by
              rw [Real.sq_sqrt]
              nlinarith
            have h9 : (sqrt (b * c)) ^ 2 = b * c := by
              rw [Real.sq_sqrt]
              nlinarith
            rw [h8, h9]
          _ = a * d + b * c + 2 * (sqrt (a * b * c * d)) := by
            have h10 : sqrt (a * d) * sqrt (b * c) = sqrt (a * b * c * d) := by
              rw [← Real.sqrt_mul (by positivity)]
              ring_nf
              all_goals positivity
            rw [h10]
      have h8 : (sqrt (a * c) + sqrt (b * d)) ^ 2 = a * c + b * d + 2 * (sqrt (a * b * c * d)) := by
        calc
          (sqrt (a * c) + sqrt (b * d)) ^ 2
              = (sqrt (a * c)) ^ 2 + (sqrt (b * d)) ^ 2 + 2 * (sqrt (a * c) * sqrt (b * d)) := by ring
          _ = a * c + b * d + 2 * (sqrt (a * c) * sqrt (b * d)) := by
            have h9 : (sqrt (a * c)) ^ 2 = a * c := by
              rw [Real.sq_sqrt]
              nlinarith
            have h10 : (sqrt (b * d)) ^ 2 = b * d := by
              rw [Real.sq_sqrt]
              nlinarith
            rw [h9, h10]
          _ = a * c + b * d + 2 * (sqrt (a * b * c * d)) := by
            have h11 : sqrt (a * c) * sqrt (b * d) = sqrt (a * b * c * d) := by
              rw [← Real.sqrt_mul (by positivity)]
              ring_nf
              all_goals positivity
            rw [h11]
      nlinarith [h7, h8, show 0 < a * b * c * d by positivity, Real.sqrt_nonneg (a * b * c * d), Real.sqrt_nonneg (a * b * c * d), hba, hdc]
    nlinarith [h6, Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c), Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d)]
  have h9 : y < x := by
    have hy_pos : 0 < y := by
      have h6 : 0 < sqrt (a * c) := by
        apply Real.sqrt_pos.2
        nlinarith
      have h7 : 0 < sqrt (b * d) := by
        apply Real.sqrt_pos.2
        nlinarith
      linarith [hy, h6, h7]
    have hx_pos : 0 < x := by
      have h6 : 0 < sqrt (a * b) := by
        apply Real.sqrt_pos.2
        nlinarith
      have h7 : 0 < sqrt (c * d) := by
        apply Real.sqrt_pos.2
        nlinarith
      linarith [hx, h6, h7]
    have h10 : y ^ 2 < x ^ 2 := by
      rw [hy, hx]
      have h11 : (sqrt (a * c) + sqrt (b * d)) ^ 2 = a * c + b * d + 2 * (sqrt (a * b * c * d)) := by
        calc
          (sqrt (a * c) + sqrt (b * d)) ^ 2
              = (sqrt (a * c)) ^ 2 + (sqrt (b * d)) ^ 2 + 2 * (sqrt (a * c) * sqrt (b * d)) := by ring
          _ = a * c + b * d + 2 * (sqrt (a * c) * sqrt (b * d)) := by
            have h9 : (sqrt (a * c)) ^ 2 = a * c := by
              rw [Real.sq_sqrt]
              nlinarith
            have h10 : (sqrt (b * d)) ^ 2 = b * d := by
              rw [Real.sq_sqrt]
              nlinarith
            rw [h9, h10]
          _ = a * c + b * d + 2 * (sqrt (a * b * c * d)) := by
            have h11 : sqrt (a * c) * sqrt (b * d) = sqrt (a * b * c * d) := by
              rw [← Real.sqrt_mul (by positivity)]
              ring_nf
              all_goals positivity
            rw [h11]
      have h12 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = a * b + c * d + 2 * (sqrt (a * b * c * d)) := by
        calc
          (sqrt (a * b) + sqrt (c * d)) ^ 2
              = (sqrt (a * b)) ^ 2 + (sqrt (c * d)) ^ 2 + 2 * (sqrt (a * b) * sqrt (c * d)) := by ring
          _ = a * b + c * d + 2 * (sqrt (a * b) * sqrt (c * d)) := by
            have h9 : (sqrt (a * b)) ^ 2 = a * b := by
              rw [Real.sq_sqrt]
              nlinarith
            have h10 : (sqrt (c * d)) ^ 2 = c * d := by
              rw [Real.sq_sqrt]
              nlinarith
            rw [h9, h10]
          _ = a * b + c * d + 2 * (sqrt (a * b * c * d)) := by
            have h11 : sqrt (a * b) * sqrt (c * d) = sqrt (a * b * c * d) := by
              rw [← Real.sqrt_mul (by positivity)]
              ring_nf
              all_goals positivity
            rw [h11]
      nlinarith [h11, h12, show 0 < a * b * c * d by positivity, Real.sqrt_nonneg (a * b * c * d), Real.sqrt_nonneg (a * b * c * d), hba, hcb, show 0 < c by linarith, show 0 < b by linarith, show 0 < a by linarith, show 0 < d by linarith]
    nlinarith [h10, Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d)]
  constructor
  · linarith [h3]
  · linarith [h9]