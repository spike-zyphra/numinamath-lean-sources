import Mathlib

theorem algebra_241603 {A B C : ℝ}
    (hA : A = (16 * Real.sqrt 2) ^ ((1 : ℝ) / 3))
    (hB : B = Real.sqrt (9 * (9 ^ ((1 : ℝ) / 3))))
    (hC : C = ((2 ^ ((1 : ℝ) / 5)) ^ 2) ^ 2) :
    A ^ 2 + B ^ 3 + C ^ 5 = 105 := by

  have h1 : A = (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [hA]
    have h2 : (16 * Real.sqrt 2 : ℝ) = (2 : ℝ) ^ (9 / 2 : ℝ) := by
      have h3 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h3]
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num]
      rw [← Real.rpow_add]
      norm_num
      all_goals norm_num
    rw [h2]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have hA2 : A ^ 2 = 8 := by
    rw [h1]
    have h4 : ((2 : ℝ) ^ (3 / 2 : ℝ) ) ^ 2 = (2 : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h4]
    norm_num
  have hB3 : B ^ 3 = 81 := by
    rw [hB]
    have h5 : Real.sqrt (9 * (9 : ℝ) ^ ((1 : ℝ) / 3) ) = (9 : ℝ) ^ (2 / 3 : ℝ) := by
      have h10 : (9 * (9 : ℝ) ^ ((1 : ℝ) / 3) ) = (9 : ℝ) ^ (4 / 3 : ℝ) := by
        have h11 : (9 * (9 : ℝ) ^ ((1 : ℝ) / 3) ) = (9 : ℝ) ^ (1 : ℝ) * (9 : ℝ) ^ (1 / 3 : ℝ) := by 
          have h12 : (9 : ℝ) ^ (1 : ℝ) = (9 : ℝ) := by simp
          rw [h12]
          <;> ring_nf 
        have h12 : (9 : ℝ) ^ (1 : ℝ) * (9 : ℝ) ^ (1 / 3 : ℝ) = (9 : ℝ) ^ (4 / 3 : ℝ) := by 
          rw [← Real.rpow_add]
          norm_num
          all_goals norm_num
        rw [h11, h12]
      have h4 : Real.sqrt ((9 * (9 : ℝ) ^ ((1 : ℝ) / 3) ) ) = Real.sqrt ((9 : ℝ) ^ (4 / 3 : ℝ) ) := by 
        rw [h10]
      have h6 : Real.sqrt ((9 : ℝ) ^ (4 / 3 : ℝ) ) = (9 : ℝ) ^ (2 / 3 : ℝ) := by
        have h7 : Real.sqrt ((9 : ℝ) ^ (4 / 3 : ℝ) ) = ((9 : ℝ) ^ (4 / 3 : ℝ) ) ^ (1 / 2 : ℝ) := by 
          rw [Real.sqrt_eq_rpow]
        rw [h7]
        have h8 : ((9 : ℝ) ^ (4 / 3 : ℝ) ) ^ (1 / 2 : ℝ) = (9 : ℝ) ^ (4 / 3 * (1 / 2) : ℝ) := by 
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        rw [h8]
        norm_num
      rw [h4, h6]
    rw [h5]
    have h6 : ((9 : ℝ) ^ (2 / 3 : ℝ) ) ^ 3 = (9 : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h6]
    norm_num
  have hC5 : C ^ 5 = 16 := by
    rw [hC]
    have h7 : ((2 ^ ((1 : ℝ) / 5) ) ^ 2) ^ 2 = (2 : ℝ) ^ (4 / 5 : ℝ) := by
      rw [show ((2 : ℝ) ^ (1 / 5 : ℝ) ) ^ 2 = (2 : ℝ) ^ (2 / 5 : ℝ) by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      ]
      rw [show ((2 : ℝ) ^ (2 / 5 : ℝ) ) ^ 2 = (2 : ℝ) ^ (4 / 5 : ℝ) by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      ]
    rw [h7]
    have h8 : ((2 : ℝ) ^ (4 / 5 : ℝ) ) ^ 5 = (2 : ℝ) ^ (4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num 
    rw [h8]
    norm_num
  rw [hA2, hB3, hC5]
  norm_num