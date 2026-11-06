import Mathlib

theorem algebra_186966 (x : ℝ) (hx : x > 0) :
    (Real.sqrt x + x ^ ((1 : ℝ) / 3)) / (Real.sqrt x - x ^ ((1 : ℝ) / 3)) = 3 ↔
    x = 64 := by
  constructor
  · -- Assume the equation holds, prove x = 64
    intro h_eq
    have h1 : Real.sqrt x - x ^ ((1 : ℝ) / 3) ≠ 0 := by 
      by_contra h1
      have h2 : (Real.sqrt x + x ^ ((1 : ℝ) / 3)) / (Real.sqrt x - x ^ ((1 : ℝ) / 3)) = 0 := by
        rw [h1]
        norm_num
      linarith
    have h_eq1 : Real.sqrt x + x ^ ((1 : ℝ) / 3) = 3 * (Real.sqrt x - x ^ ((1 : ℝ) / 3)) := by 
      field_simp [h1] at h_eq ⊢
      linarith 
    have h_eq2 : -2 * Real.sqrt x + 4 * x ^ ((1 : ℝ) / 3) = 0 := by
      linarith
    have h_eq3 : 2 * x ^ ((1 : ℝ) / 3) = Real.sqrt x := by 
      linarith 
    have h2 : Real.sqrt x = x ^ ((1 : ℝ) / 2) := by 
      rw [Real.sqrt_eq_rpow]
    rw [h2] at h_eq3 
    have h3 : (2 * x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 2)) ^ 3 := by
      have h4 : (2 * x ^ ((1 : ℝ) / 3)) = (x ^ ((1 : ℝ) / 2)) := by 
        linarith 
      rw [h4]
    have h4 : (2 * x ^ ((1 : ℝ) / 3)) ^ 3 = 8 * x := by 
      calc 
        (2 * x ^ ((1 : ℝ) / 3)) ^ 3 = 8 * (x ^ ((1 : ℝ) / 3)) ^ 3 := by ring 
        _ = 8 * ((x ^ ((1 : ℝ) / 3)) ^ 3) := by ring 
        _ = 8 * x := by 
          have h5 : ((x ^ ((1 : ℝ) / 3)) ^ 3) = x := by 
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num 
            all_goals linarith 
          rw [h5]
    have h5 : (x ^ ((1 : ℝ) / 2)) ^ 3 = x ^ ((3 / 2 : ℝ)) := by 
      calc 
        (x ^ ((1 : ℝ) / 2)) ^ 3 = (x ^ ((1 / 2 : ℝ)) ) ^ 3 := by norm_num 
        _ = x ^ (3 * (1 / 2 : ℝ)) := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf 
          all_goals linarith 
        _ = x ^ ((3 / 2 : ℝ)) := by norm_num 
    rw [h4] at h3 
    rw [h5] at h3 
    have h6 : x ^ ((3 / 2 : ℝ)) - 8 * x = 0 := by 
      linarith 
    have h7 : x ^ ((3 / 2 : ℝ)) = x * (x ^ ((1 / 2 : ℝ))) := by 
      calc 
        x ^ ((3 / 2 : ℝ)) = x ^ (1 / 2 + 1 : ℝ) := by norm_num 
        _ = x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) := by 
          rw [Real.rpow_add]
          ring_nf 
          all_goals linarith 
        _ = x ^ (1 / 2 : ℝ) * x := by 
          simp 
        _ = x * (x ^ ((1 / 2 : ℝ))) := by 
          ring 
    have h8 : x * (x ^ ((1 / 2 : ℝ)) - 8) = 0 := by 
      calc 
        x * (x ^ ((1 / 2 : ℝ)) - 8) = x * x ^ ((1 / 2 : ℝ)) - x * 8 := by ring 
        _ = x ^ ((3 / 2 : ℝ)) - (8 * x) := by 
          rw [show x * x ^ ((1 / 2 : ℝ)) = x ^ ((3 / 2 : ℝ)) by 
            rw [h7]
          ]
          <;> ring 
        _ = (x ^ ((3 / 2 : ℝ)) - 8 * x) := by ring 
        _ = (0 : ℝ) := by 
          linarith [h6]
    cases' (mul_eq_zero.mp h8) with h9 h10 
    · -- Case where x = 0
      linarith 
    · -- Case where x ^ ((1 / 2 : ℝ)) - 8 = 0
      have h11 : x ^ ((1 / 2 : ℝ)) = 8 := by 
        linarith 
      have h12 : x = 64 := by
        calc 
          x = (x ^ ((1 / 2 : ℝ))) ^ (2 : ℝ) := by 
            rw [← Real.rpow_mul]
            norm_num 
            all_goals linarith 
          _ = (8) ^ (2 : ℝ) := by 
            rw [h11] 
          _ = (64 : ℝ) := by 
            norm_num 
      linarith
  · -- Backward direction, prove the equation
    intro h_eq 
    rw [h_eq] 
    have h1 : Real.sqrt (64 : ℝ) = 8 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    have h2 : ((64 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = 4 := by 
      rw [show (64 : ℝ) = (4 : ℝ) ^ (3 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      norm_num 
      all_goals norm_num 
    rw [h1, h2]
    norm_num