import Mathlib

theorem algebra_235297 {a b : ℝ} (ha : 1 < a) (hb : 0 < b ∧ ∃ q : ℚ, b = q)
    (h : a ^ b + a ^ (-b) = 2 * Real.sqrt 3) :
    a ^ b - a ^ (-b) = 2 * Real.sqrt 2 := by

  have h1 : (a ^ b + a ^ (-b)) ^ 2 = 12 := by
    calc
      (a ^ b + a ^ (-b)) ^ 2 = (2 * Real.sqrt 3) ^ 2 := by rw [h]
      _ = 4 * (Real.sqrt 3) ^ 2 := by ring
      _ = 4 * 3 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 12 := by norm_num

  have h2 : (a ^ b - a ^ (-b)) ^ 2 = 8 := by 
    have h2 : (a ^ b - a ^ (-b)) ^ 2 = (a ^ b + a ^ (-b)) ^ 2 - 4 := by
      have h3 : (a ^ b + a ^ (-b)) ^ 2 = (a ^ b) ^ 2 + (a ^ (-b)) ^ 2 + 2 * (a ^ b * a ^ (-b)) := by ring
      have h4 : (a ^ b - a ^ (-b)) ^ 2 = (a ^ b) ^ 2 + (a ^ (-b)) ^ 2 - 2 * (a ^ b * a ^ (-b)) := by ring
      have h5 : a ^ b * a ^ (-b) = 1 := by 
        have h6 : a ^ b * a ^ (-b) = a ^ (b + (-b)) := by 
          rw [← Real.rpow_add]
          ring_nf
          all_goals linarith
        rw [h6]
        norm_num
      rw [h4]
      rw [h3]
      linarith [h5]
    rw [h2, h1]
    all_goals norm_num

  have h3 : a ^ b - a ^ (-b) > 0 := by
    have h4 : a ^ b > a ^ (-b) := by
      have h5 : b > -b := by
        linarith [hb.1]
      have h6 : a > 1 := ha
      have h7 : a ^ b > a ^ (-b) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      linarith [h7]
    linarith

  have h4 : a ^ b - a ^ (-b) = Real.sqrt 8 := by 
    have h4 : (a ^ b - a ^ (-b)) ^ 2 = 8 := h2
    have h3' : a ^ b - a ^ (-b) ≥ 0 := by linarith [h3]
    have h5 : Real.sqrt ((a ^ b - a ^ (-b)) ^ 2) = Real.sqrt 8 := by 
      rw [h4]
    have h6 : Real.sqrt ((a ^ b - a ^ (-b)) ^ 2) = a ^ b - a ^ (-b) := by 
      rw [Real.sqrt_sq]
      linarith [h3']
    have h6' : Real.sqrt 8 ≥ 0 := Real.sqrt_nonneg 8
    nlinarith [h5, h6, h6']

  have h5 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h5] at h4 
  linarith