import Mathlib

theorem algebra_10991 : {n : ℝ | 10 ^ n = 10 ^ (-5 : ℤ) * √(10 ^ 73 / 0.001)} = {33} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume 10^n = 10^(-5) * √(10^73 / 0.001), prove n = 33
    intro h
    have h1 : √ (10 ^ 73 / (0.001 : ℝ)) = (10 : ℝ) ^ (38 : ℝ) := by
      have h2 : (10 ^ 73 / (0.001 : ℝ) ) = (10 : ℝ) ^ (76 : ℝ) := by
        norm_num
      rw [h2]
      have h3 : √ ( (10 : ℝ) ^ (76 : ℝ) ) = (10 : ℝ) ^ (38 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have h4 : ( (10 : ℝ) ^ (76 : ℝ) ) ^ (1 / 2 : ℝ) = (10 : ℝ) ^ (38 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        linarith
      linarith
    have h2 : (10 : ℝ) ^ (-5 : ℤ) = (10 ^ (-5 : ℝ) ) := by
      norm_num
    have h3' : (10 ^ (-5 : ℤ) * √ (10 ^ 73 / (0.001 : ℝ)) ) = (10 : ℝ) ^ (33 : ℝ) := by
      rw [h1, h2]
      have h4 : (10 ^ (-5 : ℝ) ) * (10 ^ (38 : ℝ) ) = (10 : ℝ) ^ (33 : ℝ) := by
        rw [← Real.rpow_add]
        norm_num
        all_goals linarith
      linarith [h4]
    rw [h3'] at h
    have h4 : n = 33 := by
      apply_fun (Real.logb (10 : ℝ) ) at h
      have h4 : Real.logb (10 : ℝ) ((10 : ℝ) ^ (n : ℝ) ) = Real.logb (10 : ℝ) ((10 : ℝ) ^ (33 : ℝ) ) := by
        linarith [h]
      have h5 : Real.logb (10 : ℝ) ((10 : ℝ) ^ (n : ℝ) ) = n := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h6 : Real.logb (10 : ℝ) ((10 : ℝ) ^ (33 : ℝ) ) = (33 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h5, h6] at h4
      linarith
    linarith
  · -- Show that if n = 33, then 10^n = 10^(-5) * √(10^73 / 0.001)
    intro h
    rw [h]
    have h1 : √ (10 ^ 73 / (0.001 : ℝ)) = (10 : ℝ) ^ (38 : ℝ) := by
      have h2 : (10 ^ 73 / (0.001 : ℝ) ) = (10 : ℝ) ^ (76 : ℝ) := by
        norm_num
      rw [h2]
      have h3 : √ ( (10 : ℝ) ^ (76 : ℝ) ) = (10 : ℝ) ^ (38 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have h4 : ( (10 : ℝ) ^ (76 : ℝ) ) ^ (1 / 2 : ℝ) = (10 : ℝ) ^ (38 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        linarith
      linarith
    have h2 : (10 : ℝ) ^ (-5 : ℤ) = (10 ^ (-5 : ℝ) ) := by
      norm_num
    have h3' : (10 ^ (-5 : ℤ) * √ (10 ^ 73 / (0.001 : ℝ)) ) = (10 : ℝ) ^ (33 : ℝ) := by
      rw [h1, h2]
      have h4 : (10 ^ (-5 : ℝ) ) * (10 ^ (38 : ℝ) ) = (10 : ℝ) ^ (33 : ℝ) := by
        rw [← Real.rpow_add]
        norm_num
        all_goals linarith
      linarith [h4]
    linarith [h3']